#!/usr/bin/env python3
"""New composition search: diagonal-vacuity emitters plus direct negation.

This is a bounded synthesis screen, not a proof of a state lower bound.
The imported compiler, local fold checker, and symbolic runtime retain their
original provenance.  Only the composition/screen below is new.
"""
from pathlib import Path
import sys, json, random, math, time, argparse, hashlib

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'inputs/axioms'
sys.path.insert(0,str(BASE/'search'))
from support import *

INC7=('leaf','inc',7)
NTREE=(INC7,(INC7,'node64'))
raw['N']=NTREE
original_raw=c.raw_nodes
def with_N():
    d=original_raw();d['N']=NTREE;return d
c.raw_nodes=with_N
c.MACROS['node64']=106
c.MACROS[INC7]=82
pair=(INC,INC);quad=(pair,pair)
c.MACROS[pair]=99;c.MACROS[quad]=190

def build(t):
    old,labels=c.machine()
    rows={(q,b):a for(q,b),a in old.items()if q<1300}
    index={};shape={}
    def state(t):
        if t=='N':return state(NTREE)
        if t in c.MACROS:return c.MACROS[t]
        if t in index:return index[t]
        if not c.isnode(t):raise ValueError(t)
        q=2000+len(index);index[t]=q;shape[q]=t
        for b,ch in enumerate(t):
            rows[q,b]=(0,False,302)if ch==BREAK else(b,True,state(ch))
        return q
    root=state(t);rows[101,1]=(1,True,root)
    return rows,index,shape
c.build=build

def composed(t,anchor):
    w=tree_word(t);hits=[i for i in range(len(w)-2)if w[i:i+3]==('node49',INC,'node65')]
    assert len(hits)==8,(len(w),hits)
    new={i:None for j in hits for i in range(j,j+3)}
    for i in hits:new[i+anchor]='N'
    n=0
    def prune(t):
        nonlocal n
        if c.isnode(t):
            a,b=prune(t[0]),prune(t[1])
            return b if a is None else a if b is None else(a,b)
        out=new.get(n,t);n+=1;return out
    ans=prune(t)
    expect=[];i=0
    while i<len(w):
        if i in hits:expect.append('N');i+=3
        else:expect.append(w[i]);i+=1
    assert tree_word(ans)==tuple(expect)
    return ans

def cost(t,exact=False):
    h,l,m,mi,_=attrs(t);ch=list(nodes(t));rows,index,shape=c.build(t)
    n=len(shape);ops=c.opportunities_fast(rows,shape);optim=len(c.max_matching(ops))
    penalty=5*bad(t)+4*max(0,m-6)+4*max(0,mi-5)+max(0,h-38)
    if exact or(n-optim<=65 and penalty<=3):
        chosen=bestcompatible_all(rows,shape);optim=len(chosen)
    return n-optim+penalty,n,optim,ch,penalty

def snapshot(t,name):
    rows,idx,shape=c.build(t);chosen=bestcompatible_all(rows,shape)
    rr,ali=apply(rows,chosen)
    ss,ins,cs=c.source(t)
    check=c.validate(rr,cs)
    out=HERE/'direct_diagonal'/name;out.mkdir(parents=True,exist_ok=True)
    (out/'grammar.json').write_text(json.dumps(encode(t),indent=2)+'\n')
    (out/'folds.json').write_text(json.dumps(chosen,indent=2)+'\n')
    (out/'check.json').write_text(json.dumps(check,indent=2)+'\n')
    (out/'sites.json').write_text(json.dumps([[''.join(map(str,p)),{'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}[op],arg]for p,op,arg in ss],separators=(',',':'))+'\n')
    (out/'machine.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rr.items())))
    receipt={'state_count':len(rr)//2,'reader_nodes':len(shape),'folds':len(chosen),'sites':len(ss),'check':check,'grammar_sha256':hashlib.sha256((out/'grammar.json').read_bytes()).hexdigest()}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('SNAPSHOT',name,receipt,flush=True)
    return receipt

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--cycles',type=int,default=20);ap.add_argument('--iterations',type=int,default=1200);ap.add_argument('--seed',type=int,default=6236814);ap.add_argument('--seconds',type=int,default=900);args=ap.parse_args()
    random.seed(args.seed)
    starts=[BASE/'search'/f'{f}.grammar.json'for f in['verified196','separate196']]
    starts+=sorted((BASE/'search/ties').glob('*.grammar.json'))
    pool=[];seen=set()
    for p in starts:
        t0=c.read_grammar(p)
        for a in range(3):
            t=composed(t0,a)
            if t not in seen:
                seen.add(t);pool.append((t,str(p.name)+':'+str(a)))
    ranked=sorted([(cost(t)[0],t,f)for t,f in pool],key=lambda x:x[0]);best=ranked[0][0]
    print('START',[(v,f,cost(t)[:3],attrs(t))for v,t,f in ranked[:12]],'unique',len(pool),flush=True)
    out=HERE/'direct_diagonal';out.mkdir(exist_ok=True)
    (out/'initial.json').write_text(json.dumps([{'cost':v,'family':f,'reader_nodes':cost(t)[1],'folds':cost(t)[2],'attrs':attrs(t)}for v,t,f in ranked],indent=2)+'\n')
    pool=[(t,f)for v,t,f in ranked if v<=best+3]
    start=time.monotonic();besttree=ranked[0][1];records=[]
    for cycle in range(args.cycles):
        if time.monotonic()-start>args.seconds:break
        t,family=random.choice(pool);v,n,f,ch,penalty=cost(t)
        for j in range(args.iterations):
            x=random.choice(ch);opts=list(rotations(x))
            if not opts:continue
            nt=repl(t,x,random.choice(opts));nv,nn,nf,nch,np=cost(nt);temp=.06+.65*(1-j/args.iterations)
            if nv<=v or random.random()<math.exp((v-nv)/temp):
                t,v,n,f,ch,penalty=nt,nv,nn,nf,nch,np
                if v<best:
                    best=v;besttree=t;record={'cost':v,'nodes':n,'folds':f,'penalty':penalty,'family':family,'cycle':cycle,'j':j,'seconds':time.monotonic()-start};records.append(record)
                    print('BEST',record,flush=True);(out/f'best{v}.grammar.json').write_text(json.dumps(encode(t),indent=2)+'\n')
                if v<=best+1 and t not in seen and len(pool)<160 and random.random()<.05:seen.add(t);pool.append((t,family))
                if v<=61 and penalty==0:
                    r=snapshot(t,'candidate'+str(134+v))
                    if r['check']['ok']:
                        print('SUCCESS',r,flush=True);return
        print('CYCLE',cycle,'best',best,'current',v,n,f,'pool',len(pool),'seconds',time.monotonic()-start,flush=True)
    (out/'search_summary.json').write_text(json.dumps({'best_cost':best,'parameters':vars(args),'improvements':records,'seconds':time.monotonic()-start,'status':'bounded screen; no sub196 result'},indent=2)+'\n')
    snapshot(besttree,'best_screen')

if __name__=='__main__':main()
