#!/usr/bin/env python3
"""Preserve the six existing reader-fold pairs during AX reassociation."""
from rotate_search import *
import math,sys,time,random

FROZEN={tree(n) for n in ['x4','x7','x5','x15','x11','x31','x23','x55','x25','x45','x50','x51']}
BASE=tree('x67');BASENS=nodes(BASE)
def stats(t):
    ns=nodes(t)
    return len(ns)-int(('i','i') in ns),len(ns-BASENS),len(FROZEN-ns)

if __name__=='__main__':
    rng=random.Random(40991);base=BASE;best=(68,0,0);besttree=base
    budget=int(sys.argv[1]) if len(sys.argv)>1 else 1000000
    t=base;score=68;start=time.time();print('baseline',best,flush=True)
    for it in range(budget):
        if it%20000==0:
            t=besttree;n,nov,f=best;score=n+nov*.001+f*5
        p,q=rng.choice(paths(t));a,b=q
        if q in FROZEN:continue
        if rng.randrange(2):
            if not isinstance(a,tuple):continue
            u,v=a;new=(u,(v,b))
        else:
            if not isinstance(b,tuple):continue
            u,v=b;new=((a,u),v)
        cand=replace(t,q,new) if rng.random()<.65 else replace_one(t,p,new)
        n,nov,f=stats(cand)
        if f:continue
        candscore=n+nov*.001
        temp=.5*(1-(it%20000)/20000)+.01
        if candscore<=score or rng.random()<math.exp((score-candscore)/temp):t=cand;score=candscore
        if (n,nov,f)<best:
            best=n,nov,f;besttree=cand;assert expand(cand)==WORD
            output(cand,Path(__file__).with_name('frozen_best.json'))
            print('best',best,'iter',it,'secs',round(time.time()-start,3),flush=True)
    print('done',best,'secs',round(time.time()-start,3),flush=True)
