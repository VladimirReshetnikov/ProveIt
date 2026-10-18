#!/usr/bin/env python3
"""Research search: certify recurrent instruction semantics after state folds.

The state search is bounded; accepted universal macro checks use the inherited
literal/self-loop/list induction rules. Blank initialization is a separate gate.
"""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'baseline/zfc-context246'
sys.path.insert(0, str(BASE/'code'))
import check_macro_inductions as m
import review_affine_source as v
from rebuild_machines import read_table, encode

OLD, START = read_table(BASE/'machine/zfc_prefix246_old.tm')
STATES = sorted({q for q,b in OLD})
AFFINE = v.module(BASE/'sources/prior/prefix_affine.py')
_, SITES = v.parse_source(BASE/'sources/Prog254.v')
MARKS = (60,44,31,56,38,40,28,64,69)


def infer_finish(name, begin, end, allow_lists=False):
    """Derive the first exact frame endpoint, recording its actual state."""
    c = begin.copy()
    cost, motion, trace = m.E(), m.E(), []
    def frame(conf):
        return conf.side, m.norm(conf.left, True), m.norm(conf.right, True)
    want = frame(end)
    for _ in range(600):
        if frame(c) == want:
            return c.state, dict(name=name, universal=True, steps=str(cost),
                motion=str(motion), exit_state=c.state, trace=trace)
        answer = m.apply_list_induction(c, cost, motion, trace) if allow_lists else None
        if answer is None:
            cost, motion = m.literal_or_power(c, cost, motion, trace)
        else:
            cost, motion = answer
    raise AssertionError((name, 'proof did not close'))


def derive(T, rep=lambda q:q):
    m.TABLE = T
    m.DERIVED.clear(); m.BLOCK_PROOFS.clear(); m.WORD_IDENTITY_PROVED = False
    # These four looping interfaces are deliberately held fixed in this search.
    m.prove_blocks(); m.prove_word_identity()
    x,y = m.E.var('x'),m.E.var('y')
    a,b = m.Blocks('B','pre'),m.Blocks('B','suf')
    l,z = m.Context('arbitrary_left'),m.Blank()
    specifications = [
        ('positive',m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0),m.ones(x+1),b,z]),
         m.Conf(48,'L',[m.bit(1),l],[a]+m.B(x)+[b,z])),
        ('zero',m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0)]+m.B(y)+[b,z]),
         m.Conf(112,'L',[l],[a]+m.B(m.E())+m.B(y)+[b,z])),
        ('increment',m.Conf(73,'R',[l],[a,m.bit(0),m.bit(0),m.ones(x),b,z]),
         m.Conf(48,'L',[l],[a]+m.B(x+1)+[b]+m.B(m.E(1))+[z])),
    ]
    exits, proofs = {}, []
    for name,start,end in specifications:
        q, proof = infer_finish(name,start,end,True)
        exits[name]=str(q);proofs.append(proof)
    values=[m.E.var('r'+str(i)) for i in range(9)]
    suffix=[m.Blocks('B','spare'),z]
    file=[atom for val in values for atom in m.B(val)]+suffix
    mark_exits = {}
    for r,entry in enumerate(MARKS):
        wanted=[atom for val in values[:r] for atom in m.B(val)]
        wanted += [m.bit(0),m.bit(0),m.ones(values[r])]
        wanted += [atom for val in values[r+1:] for atom in m.B(val)]+suffix
        q,proof = infer_finish('mark_'+str(r),m.Conf(rep(entry),'R',[l],file.copy()),
            m.Conf(2 if r==0 else 6,'L',[l],wanted))
        mapped = str(rep(entry))
        assert mapped not in mark_exits, ('ambiguous mark interface',mapped)
        mark_exits[mapped]=(r,str(q));proofs.append(proof)
    def oracle(q, branch, state):
        if state==('plain',None) and q in mark_exits:
            r,out=mark_exits[q]
            return out,('mark',r),0
        if state[0]=='mark':
            r=state[1]
            if not 0<=r<9:return None
            if q=='73':return exits['increment'],('plain',('inc',r)),0
            if q=='95' and branch is not None and branch[0]==r:
                if branch[1]:return exits['zero'],('plain',None),0
                return exits['positive'],('plain',('dec',r)),1
        return None
    return oracle,dict(exits=exits,mark_exits=mark_exits,proofs=proofs)


def verify(T, rep=lambda q:q):
    oracle, macros = derive(T,rep)
    AFFINE.oracle=oracle
    table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in T.items()}
    result=v.check_sites(AFFINE,table,SITES)
    return dict(instructions=result,macros=macros)


def shared_branch(q,p):
    def row(x,b):
        w,d,t=OLD[x,b]
        return w,d,p if t==q else t
    return any(row(q,b)==row(p,b) for b in (0,1))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--all-pairs',action='store_true')
    ap.add_argument('--remove',type=int)
    ap.add_argument('--mixed',action='store_true')
    args=ap.parse_args()
    began=time.monotonic();counts=Counter();found=[]
    protected={48,63,73,83,95,109,112,131,96}
    candidates=[]
    if args.mixed:
        assert args.remove is not None
        q=args.remove
        entries=[k for k,vv in OLD.items() if vv[2]==q and k[0]!=q]
        targets=[p for p in STATES if p!=q and shared_branch(q,p)]
        print('MIXED',q,'entries',entries,'targets',targets,flush=True)
        for choices in itertools.product(targets,repeat=len(entries)):
            if q in MARKS:continue
            T={k:r for k,r in OLD.items() if k[0]!=q}
            for k,p in zip(entries,choices):
                w,d,_=T[k];T[k]=(w,d,p)
            if any(t==q for w,d,t in T.values()):continue
            candidates.append((q,choices,T,lambda x:x))
    else:
        for q in STATES:
            if q in protected or (args.remove is not None and q!=args.remove):continue
            for p in STATES:
                if p==q or (not args.all_pairs and not shared_branch(q,p)):continue
                rep=lambda x,q=q,p=p:p if x==q else x
                T={k:(w,d,rep(t)) for k,(w,d,t) in OLD.items() if k[0]!=q}
                candidates.append((q,p,T,rep))
    print('Candidates',len(candidates),flush=True)
    for i,(q,p,T,rep) in enumerate(candidates):
        try:
            result=verify(T,rep)
            label=str(q)+'_to_'+('_'.join(map(str,p)) if isinstance(p,tuple) else str(p))
            (ROOT/('fold_'+label+'.tm')).write_text(encode(T,rep(START)))
            (ROOT/('fold_'+label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
            found.append((q,p));counts['PASS']+=1
            print('SUCCESS',q,p,flush=True)
        except Exception as e:
            key=str(e)
            counts[type(e).__name__+': '+key[:90]]+=1
        if (i+1)%100==0:print('done',i+1,'seconds',round(time.monotonic()-began,2),'found',found,flush=True)
    summary=dict(candidates=len(candidates),found=found,seconds=time.monotonic()-began,counts=dict(counts))
    path=ROOT/('fold-search-'+('mixed'+str(args.remove) if args.mixed else ('uniform'+str(args.remove)))+'.json')
    path.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()
