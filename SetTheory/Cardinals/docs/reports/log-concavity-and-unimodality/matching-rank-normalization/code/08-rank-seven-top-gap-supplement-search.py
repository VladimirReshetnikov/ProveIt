#!/usr/bin/env python3
"""Rank-seven forced-cover endpoint-set diagnostics. No matching multiplicities."""
from itertools import combinations, combinations_with_replacement
from functools import lru_cache
from collections import Counter
from math import comb
from random import Random
from pathlib import Path
import json,time
import numpy as np

@lru_cache(None)
def endpoints(cols):
    states={0}
    for c in cols:
        states={I|bit for I in states for bit in bits(c&~I)}
    return tuple(sorted(states))
def bits(x):
    while x:
        b=x&-x;x-=b;yield b

def left_signatures(left,b):
    out=[{} for j in range(b+1)];counts=Counter(left)
    for j in range(b+1):
        for J in combinations_with_replacement(sorted(counts),j):
            wt=1
            for typ,m in Counter(J).items():
                wt*=comb(counts[typ],m) if counts[typ]>=m else 0
            if not wt:continue
            sig=endpoints(J)
            if sig:out[j][sig]=out[j].get(sig,0)+wt
    return out

def coefficient_profiles(core,left,a,b,types=None):
    ls=left_signatures(tuple(left),b)
    bcols=[sum(1<<i for i,row in enumerate(core) if row>>j&1) for j in range(b)]
    out=[]
    for j in range(a+1):
        entries=[]
        for R in combinations_with_replacement(range(1,1<<a) if types is None else types,j):
            total=0
            for sz in range(a+1):
                ell=b+j-sz
                if not 0<=ell<=b:continue
                for I in combinations(range(a),sz):
                    mask=sum(1<<i for i in I)
                    good=set()
                    for BJ in combinations(range(b),ell):
                        bm=sum(1<<i for i in BJ)
                        cols=tuple(sorted([bcols[z]&mask for z in range(b) if not bm>>z&1]+[r&mask for r in R]))
                        if mask in endpoints(cols):good.add(bm)
                    total+=sum(n for sig,n in ls[ell].items() if any(x in good for x in sig))
            if total:entries.append((R,total))
        out.append(entries)
    return out

def evaluate(profiles,totals,pops):
    out=[]
    for rows in profiles:
        s=0.
        for R,c in rows:
            wt=float(c)
            for t in set(R):
                m=R.count(t);n=pops[t-1]
                wt*=comb(n,m)*(totals[t-1]/n)**m if n>=m else 0
            s+=wt
        out.append(s)
    return out

def prepare(profiles,g,pops):
    exps=[];coeff=[];degs=[]
    for j,rows in enumerate(profiles):
        for R,c in rows:
            e=[0]*g
            for t in R:e[t-1]+=1
            for t,m in enumerate(e):
                if m:c*=comb(pops[t],m)/pops[t]**m if pops[t]>=m else 0
            exps.append(e);coeff.append(c);degs.append(j)
    return np.array(exps),np.array(coeff),np.array(degs)

def sample(profiles,a,pops,rng,trials=1000, target=None):
    ex,co,de=prepare(profiles,(1<<a)-1,pops)
    # Smooth gamma/log-uniform activity families, then local log-coordinate descent.
    W=rng.uniform(-6,6,(trials,(1<<a)-1))
    W[:trials//2]=rng.normal(0,2,(trials//2,(1<<a)-1))
    val=np.exp(W@ex.T)*co
    C=np.stack([val[:,de==j].sum(axis=1) for j in range(a+1)],axis=1)
    factors=np.array([(7-(a-j))*(a-j+2)/((7-(a-j)+1)*(a-j+1)) for j in []])
    # Gap j: actual index b+j, factor (i+1)(8-i)/(i(7-i)).
    b=7-a
    f=np.array([((b+j+1)*(8-b-j))/((b+j)*(7-b-j)) for j in range(1,a)])
    rat=C[:,1:-1]**2/(C[:,:-2]*C[:,2:])/f
    if target is not None:
        rat[:,[j for j in range(a-1) if j!=target-1]]=1e100
    where=np.unravel_index(np.argmin(rat),rat.shape)
    best=float(rat[where]);w=W[where[0]].copy();which=where[1]+1
    def objective(w):
        vals=np.exp(ex@w)*co
        cc=np.array([vals[de==j].sum() for j in range(a+1)])
        rr=cc[1:-1]**2/(cc[:-2]*cc[2:])/f
        if target is not None:
            rr[[j for j in range(a-1) if j!=target-1]]=1e100
        return float(rr.min()),cc,int(rr.argmin()+1)
    for step in [2.,1.,.5,.2,.1]:
        changed=True
        while changed:
            changed=False
            for z in rng.permutation(len(w)):
                for sign in [-1,1]:
                    ww=w.copy();ww[z]+=sign*step
                    if abs(ww[z])>14:continue
                    v,cc,j=objective(ww)
                    if v<best-1e-10:best,w,which=v,ww,j;changed=True
    best,C,which=objective(w)
    return best,C.tolist(),which,np.exp(w).tolist()

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--a',type=int,default=3);ap.add_argument('--cases',type=int,default=500);ap.add_argument('--trials',type=int,default=500);ap.add_argument('--target',type=int);ap.add_argument('--diffuse-left',action='store_true');args=ap.parse_args()
    a=args.a;b=7-a;rng=Random(814434+a);nrng=np.random.default_rng(591+a);best=100;start=time.time();history=[]
    for case in range(args.cases):
        core=[rng.randrange(1<<b) for _ in range(a)]
        left=[1<<i for i in range(b)]+[rng.randrange(1,1<<b) for _ in range(rng.randint(0,8))]
        if case%5==0:left=[(1<<b)-1]*rng.randint(b,b+24)
        if case%11==0:core=[(1<<b)-1]*a
        if args.diffuse_left:
            left=[1<<i for i in range(b)]
            for typ in range(1,1<<b):left.extend([typ]*rng.choice([0,1,2,5,20,100,1000]))
        prof=coefficient_profiles(core,left,a,b)
        pops=[rng.choice([1,2,3,10,100000]) for _ in range((1<<a)-1)]
        value,C,gap,totals=sample(prof,a,pops,nrng,args.trials,args.target)
        if value<best:
            best=value;item=dict(case=case,a=a,b=b,core=core,left_counts=dict(Counter(left)),populations=pops,right_totals=totals,C=C,gap=gap,normalized_ratio=value);history.append(item)
            Path(__file__).with_name(f'diagnostics_a{a}_target{args.target}_diffuse{args.diffuse_left}.json').write_text(json.dumps(dict(cases=case+1,best=item,records=history),indent=2)+'\n')
            print('BEST',json.dumps(item),flush=True)
        if value<1-1e-8:break
        if case%10==0:print('PROGRESS',case,'seconds',time.time()-start,'cache',endpoints.cache_info(),flush=True)
    print('DONE',case+1,best,time.time()-start,flush=True)
if __name__=='__main__':main()
