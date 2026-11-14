#!/usr/bin/env python3
"""Explore exact AX-word reassociations with a five-zero marker budget.

Intermediate search only. A promising grammar is not a verified TM.
The trial counter counts sampling attempts, including repeats and samples
without a rotation. Wall-clock budgets make repeat counts machine dependent.
"""
from pathlib import Path
from functools import lru_cache
import sys, json, random, math, time, argparse

import search_support as a
l=a
RAW=l.raw_nodes()
INC=('leaf','inc',1)

def original(t='x67'):
    if isinstance(t,str) and t.startswith('x'):
        return tuple(original(c) for c in RAW[t])
    return t

@lru_cache(maxsize=500000)
def norm(t):
    if not l.isnode(t):return t
    x,y=norm(t[0]),norm(t[1])
    if x==INC and y==INC:return 'node60'
    if x=='node60' and y=='node60':return 'node61'
    return x,y

def stats(t):
    seen={}
    def rec(t):
        if not l.isnode(t):return a.attrs(t)
        if t in seen:return seen[t]
        h,x,m=rec(t[0]);h2,x2,m2=rec(t[1])
        ans=(1+max(h,h2),1+x,max(1+x,m,m2))
        seen[t]=ans;return ans
    attrs=rec(t)
    return attrs,seen

def replace(t,x,y):
    if t==x:return y
    if not l.isnode(t):return t
    return norm((replace(t[0],x,y),replace(t[1],x,y)))

def rotations(t):
    if not l.isnode(t):return []
    ans=[]
    x,y=t
    xx=RAW[x] if x in ('node60','node61') else x
    yy=RAW[y] if y in ('node60','node61') else y
    if l.isnode(xx):ans.append(norm((xx[0],(xx[1],y))))
    if l.isnode(yy):ans.append(norm(((x,yy[0]),yy[1])))
    return ans

def context_bad(t,side=1):
    if isinstance(t,str):return int(t in a.ENTRY_CONTEXT and side!=a.ENTRY_CONTEXT[t])
    if not l.isnode(t):return 0
    return context_bad(t[0],0)+context_bad(t[1],1)

def bad_prefixes(t):
    """Count bad internal left-prefix starts, weighted by occurrence."""
    if not l.isnode(t):return 0
    return int(1+a.attrs(t[0])[1]>5)+bad_prefixes(t[0])+bad_prefixes(t[1])

@lru_cache(maxsize=100000)
def cost_data(t):
    attrs,seen=stats(t);n=len(seen)
    bad=sum(max(0,la-5) for h,la,m in seen.values())
    cb=context_bad(t)
    rows,idx,shape=l.build(t)
    f=len(l.max_matching(l.opportunities_fast(rows,shape)))
    return n-f,n,f,attrs,bad,cb

def encode(t):return a.encode(t)

def main():
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=240)
    p.add_argument('--seed',type=int,default=313);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--zero',type=int,default=5);p.add_argument('--initial',type=Path)
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    rng=random.Random(args.seed);initial=norm(l.read_grammar(args.initial) if args.initial else original())
    saved_feasible=[];initialc=cost_data(initial)
    print('initial',initialc,flush=True)
    start=time.monotonic();trials=0;cycles=0;bestfeas=1000;bestnear=(1000,None)
    while time.monotonic()-start<args.seconds:
        starttree=rng.choice(saved_feasible) if saved_feasible and rng.random()<.4 else initial
        t=starttree;cd=cost_data(t);nodes=list(stats(t)[1]);penalty=rng.choice([.5,1.,1.5,2.,3.,4.])
        def score(c):
            e,n,f,(h,le,z),bad,cb=c
            if args.zero==6:bad=0 if z<=6 else bad
            return e+penalty*bad+4*cb+max(0,h-42)
        c=score(cd)
        for j in range(3000):
            trials+=1;node=rng.choice(nodes);opts=rotations(node)
            if not opts:continue
            nt=replace(t,node,rng.choice(opts));ncd=cost_data(nt);nc=score(ncd)
            temp=.08+.8*(1-j/3000)
            if nc<=c or rng.random()<math.exp((c-nc)/temp):
                t,c,cd=nt,nc,ncd;nodes=list(stats(t)[1])
            e,n,f,(h,le,z),bad,cb=ncd
            if not cb and z<=args.zero and h<=42 and e<=bestfeas:
                if e<bestfeas:
                    bestfeas=e;saved_feasible=[]
                    print('FEASIBLE',e,n,f,(h,le,z),trials,'sec',time.monotonic()-start,flush=True)
                    data=encode(nt);data['search']={'cost':ncd,'trials':trials,'seed':args.seed}
                    (args.out/f'best-{e}.json').write_text(json.dumps(data,indent=2)+'\n')
                if nt not in saved_feasible and len(saved_feasible)<30:saved_feasible.append(nt)
                if (args.zero==5 and e<=62)or(args.zero==6 and e<=61):
                    print('TARGET GRAMMAR FOUND',flush=True);return
            if nc<bestnear[0]:bestnear=(nc,nt)
            if time.monotonic()-start>=args.seconds:break
        cycles+=1
        print('cycle',cycles,'bestfeas',bestfeas,'trials',trials,'sec',time.monotonic()-start,flush=True)
    (args.out/'receipt.json').write_text(json.dumps({'trials':trials,'cycles':cycles,'best_effective_ax':bestfeas,'seconds':time.monotonic()-start,'seed':args.seed,'max_zero':args.zero},indent=2)+'\n')

if __name__=='__main__':main()
