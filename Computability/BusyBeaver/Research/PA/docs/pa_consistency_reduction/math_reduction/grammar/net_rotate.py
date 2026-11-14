#!/usr/bin/env python3
"""Minimize genuinely new AX nodes, reusing the fixed ii/iiii subtrees."""
from rotate_search import *
import math,sys,json,time,random

def nc(t):
    ns=nodes(t)
    return len(ns)-int(('i','i') in ns)-int((('i','i'),('i','i')) in ns)

if __name__=='__main__':
    rng=random.Random(910243);base=tree('x67')
    if len(sys.argv)>2:
        d=json.loads(Path(sys.argv[2]).read_text());rr=d['rules']
        def get(q):return tuple(map(get,rr[q])) if q in rr else q
        base=get(d['root'])
    best=nc(base);besttree=base
    budget=int(sys.argv[1]) if len(sys.argv)>1 else 1000000
    t=base;score=best;start=time.time();print('baseline',best,flush=True)
    for it in range(budget):
        if it%20000==0:t=besttree;score=best
        p,q=rng.choice(paths(t));a,b=q
        if rng.randrange(2):
            if not isinstance(a,tuple):continue
            u,v=a;new=(u,(v,b))
        else:
            if not isinstance(b,tuple):continue
            u,v=b;new=((a,u),v)
        cand=replace(t,q,new) if rng.random()<.6 else replace_one(t,p,new)
        s=nc(cand);delta=s-score
        temp=.4*(1-(it%20000)/20000)+.05
        if delta<=0 or rng.random()<math.exp(-delta/temp):t=cand;score=s
        if s<best:
            best=s;besttree=cand;assert expand(cand)==WORD
            output(cand,Path(__file__).with_name('net_min_best.json'))
            print('best',best,'iter',it,'secs',round(time.time()-start,3),flush=True)
    print('done',best,'secs',round(time.time()-start,3),flush=True)
