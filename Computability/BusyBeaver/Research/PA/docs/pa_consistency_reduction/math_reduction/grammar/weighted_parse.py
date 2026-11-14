#!/usr/bin/env python3
"""Discounted substring dynamic programming for shared AX parsing."""
import sys,time,random,collections,math
from pathlib import Path
from rotate_search import *

W=''.join(WORD)
FREQ=collections.Counter(W[i:j] for i in range(len(W)) for j in range(i+2,len(W)+1))
WORDS=sorted(FREQ,key=len)
SPLITS={w:tuple((w[:i],w[i:]) for i in range(1,len(w))) for w in WORDS}

def optimize(weights):
    costs={x:0 for x in set(W)};rules={}
    for w in WORDS:
        cost,l,r=min((costs[l]+costs[r],l,r) for l,r in SPLITS[w])
        costs[w]=cost+weights[w];rules[w]=l,r
    def get(w):
        if len(w)==1:return w
        l,r=rules[w];return get(l),get(r)
    return get(W)

if __name__=='__main__':
    rng=random.Random(642);start=time.time();base=tree('x67');best=68;besttree=base
    trials=int(sys.argv[1]) if len(sys.argv)>1 else 200
    weights={w:1/f for w,f in FREQ.items()}
    for k in range(trials):
        t=optimize(weights);s=len(nodes(t));count=collections.Counter(''.join(expand(q)) for p,q in paths(t))
        if s<best:
            best=s;besttree=t;output(t,Path(__file__).with_name('weighted_best.json'))
            print('best',best,'iter',k,'secs',round(time.time()-start,3),flush=True)
        if k%10==9:
            counts=collections.Counter(''.join(expand(q)) for p,q in paths(besttree))
            weights={w: (1/(counts.get(w,0)+.1)+.1*rng.random()) if rng.random()<.8 else 1/FREQ[w] for w in WORDS}
        else:
            weights={w:1/max(.1,count.get(w,0)+rng.random()*.1) for w in WORDS}
        if k%20==0:print('iter',k,'score',s,'best',best,flush=True)
    print('done',best,round(time.time()-start,3),flush=True)
