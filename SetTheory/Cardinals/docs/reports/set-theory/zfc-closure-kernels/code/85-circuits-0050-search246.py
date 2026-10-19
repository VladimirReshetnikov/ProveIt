#!/usr/bin/env python3
"""Joint decoder-layout and scanner-cost experiment on the exact Context246.

Uses the attributed source27 fingerprint reuse emitter, closed rotations, and
source63 affine contracts. This is an experiment, not a kernel certificate.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json,hashlib,sys,time,argparse,random,math
import rotate_search as rot

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[1]
BASE=PACKAGE/'reference/context246'
sys.path.insert(0,str(BASE/'sources/prior'))
import prefix_affine as affine
OLD=json.loads((HERE/'decoder_entries.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in OLD['nodes'].items()}
ROOT=OLD['root']
PHYS=(6,2,0,4,3,7,8,5,1)
BASE246={}
for line in (BASE/'machine/zfc_prefix246_old.tm').read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split();BASE246[q,int(b)]=int(w),d,t
OLD_FP={v:int(n) for n,v in OLD['fingerprints'].items()}
CONTROL_OPTIONS={}
for n,pair in NODES.items():
    for bit,e in enumerate(pair):
        if e[0] not in 'BC':continue
        counts=CONTROL_OPTIONS.setdefault((e,bit),Counter())
        for state,weight in OLD['state_entries'][str(n)].items():
            counts[BASE246[state,bit]]+=weight

def fingerprints(nodes):
    @lru_cache(None)
    def f(e):
        if e[0]=='N':
            a,b=nodes[e[1]];text='N('+f(a)+','+f(b)+')'
        else:text=':'.join(map(str,e))
        return hashlib.sha256(text.encode()).hexdigest()
    return {n:f(('N',n)) for n in nodes}

def emit(nodes,root,short=False):
    fp=fingerprints(nodes);table=BASE246.copy();entries={};allocate=256
    modal=lambda c:max(c,key=c.get)
    for n in nodes:
        f=fp[n]
        if n==root:entries[n]='96'
        elif f in OLD_FP:entries[n]=modal(OLD['state_entries'][str(OLD_FP[f])])
        else:entries[n]=str(allocate);allocate+=1
    def transition(e,bit):
        if e[0]=='N':return bit,'R',entries[e[1]]
        if e[0]=='B' and e[1]==1:return 0,'L','7' if bit==0 else '33'
        if e[0] in 'BC':return CONTROL_OPTIONS[e,bit].most_common(1)[0][0]
        return bit,'R',modal(OLD['leaf_entries'][':'.join(map(str,e))])
    for n in nodes:
        if entries[n]=='96' or fp[n] not in OLD_FP:
            for b,e in enumerate(nodes[n]):table[entries[n],b]=transition(e,b)
    if short:
        del table['74',0];del table['74',1];table['58',0]=(0,'L','84')
    return table,entries

def sites(nodes,root):
    output=[];todo=[(('N',root),'')]
    while todo:
        e,p=todo.pop()
        if e[0]=='N':
            a,b=nodes[e[1]];todo.extend([(b,p+'1'),(a,p+'0')])
        else:output.append((p,'C'+e[0],None if e[0]=='H' else e[1]))
    return output

def increment(pc):return pc[:pc.rindex('0')]+'1' if '0' in pc else None
def strip(pc,symbol,count):
    while pc and count:
        count-=pc[-1]==symbol;pc=pc[:-1]
    return pc

def cases(ss):
    out=[]
    for pc,op,l in ss:
        r=PHYS[l] if op in ('CI','CD') else l
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(r,zero) if op=='CD' else None
            if op=='CI' or (op=='CD' and not zero):successor=increment(pc)
            elif op=='CD':successor=increment(strip(pc,'0',1))
            elif op=='CB':successor=increment(strip(pc,'0',r))
            elif op=='CC':successor=strip(pc,'1',r)
            else:successor=''
            effect=('inc',r) if op=='CI' else (('dec',r) if op=='CD' and not zero else None)
            extra=int(op=='CD' and not zero)
            if successor is None:right=[('r',0,1,41+extra),('b',1),('box',('plain',effect))]
            else:right=[('b',int(b)) for b in successor]+[('r',0,1,40+extra-len(successor)),('b',1),('box',('plain',effect))]
            out.append((pc,op,l,branch,affine.canon([('b',1)],right)))
    return out

class Tracking(dict):
    def __init__(self,T):super().__init__(T);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def check(T,c,fuel=1500):
    pc,op,l,b,tgt=c
    try:
        rules,lit=affine.run(T,pc,b,tgt,halt=op=='CH',fuel=fuel)
        assert lit>0
        return None
    except (AssertionError,KeyError) as e:return str(e)

def evaluate(nodes,root,short=False,early=None):
    try:T,_=emit(nodes,root,short)
    except (KeyError,IndexError) as e:return dict(outcome='unsupported_leaf',message=str(e))
    ss=sites(nodes,root)
    if max(map(lambda x:len(x[0]),ss))>39:return dict(outcome='depth')
    cs=cases(ss);tracked=Tracking(T)
    if early:
        for j in early:
            fail=check(tracked,cs[j])
            if fail:return dict(outcome='early_fail',failed_case=j,pc=cs[j][0],error=fail)
    for i,c in enumerate(cs):
        fail=check(tracked,c)
        if fail:return dict(outcome='affine_fail',failed_case=i,pc=c[0],error=fail)
    # Macro support is proved independently; leave all its used rows live.
    macro=json.loads((BASE/'results/macro-inductions.json').read_text())
    # fixed runtime support, a conservative superset of the 42 proven rows
    core={2,4,6,7,9,10,13,14,19,20,28,29,30,31,38,40,41,42,44,48,56,57,58,60,63,64,69,73,75,83,84,95,109,112,131,255}
    if not short:core.add(74)
    runtime={str(q) for q in core}
    used={q for q,b in tracked.used}|runtime|{'96'}
    return dict(outcome='PASS',symbolic_cases=len(cs),runtime_states=len(used),used=sorted(used,key=int),table=T,sites=ss,rows_used=sorted(tracked.used))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--short',action='store_true');ap.add_argument('--single',action='store_true');ap.add_argument('--iterations',type=int,default=0);a=ap.parse_args()
    t0=time.monotonic();bcs=cases(sites(NODES,ROOT));early=[]
    T,_=emit(NODES,ROOT,True)
    for i,c in enumerate(bcs):
        if check(T,c):early.append(i)
    print('baseline failing short cases',len(early),flush=True)
    assert len(early)==36
    if not a.single and not a.iterations:
        e=evaluate(NODES,ROOT,a.short,early=early);e.pop('table',None);e.pop('sites',None);e.pop('rows_used',None);print(e);return
    results=[];wins=[];counts=Counter()
    for i,(n,e,k) in enumerate(rot.options(NODES)):
        nn,nr=rot.mutate(NODES,ROOT,n,e)
        outcome=evaluate(nn,nr,a.short,early=early)
        counts[outcome['outcome']]+=1
        if outcome['outcome']=='PASS':
            name=f'single-{i}'+('-short' if a.short else '')
            (HERE/(name+'.json')).write_text(json.dumps(dict(root=nr,nodes=nn,**{key:v for key,v in outcome.items() if key!='table'}),indent=2)+'\n')
            (HERE/(name+'.tm')).write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(outcome['table'].items(),key=lambda x:(int(x[0][0]),x[0][1]))))
            print('PASS',i,k,outcome['runtime_states'],flush=True);wins.append((i,outcome['runtime_states']))
        results.append(dict(index=i,node=n,kind=k,nodes=len(nn),zero_metrics=rot.zero_metrics(nn,nr),**{key:v for key,v in outcome.items() if key not in ('table','sites','rows_used','used')}))
        if (i+1)%20==0:print('done',i+1,dict(counts),round(time.monotonic()-t0,2),flush=True)
    (HERE/('single-results-short.json' if a.short else 'single-results.json')).write_text(json.dumps(dict(counts=counts,winners=wins,results=results,seconds=time.monotonic()-t0),indent=2)+'\n')
    print('finished',dict(counts),wins,flush=True)

if __name__=='__main__':main()
