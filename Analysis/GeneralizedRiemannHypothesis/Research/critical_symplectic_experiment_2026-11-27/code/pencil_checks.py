#!/usr/bin/env python3
"""Finite checks of independent nonsingularity in random alternating pencils.
No simulation output is a proof. Prime fields q=2,3 are implemented.
"""
import argparse, itertools, json, math, time
from pathlib import Path
import numpy as np

def projective_points(q,k):
    out=[]
    for t in itertools.product(range(q), repeat=k):
        if any(t) and next(x for x in t if x)==1:
            out.append(t)
    return np.array(out,dtype=np.int16)

def nonsing_prob(q,n):
    return math.prod(1-q**(-(2*j-1)) for j in range(1,n//2+1))

def nonsing_prob_inf(q):
    return math.prod(1-q**(-(2*j-1)) for j in range(1,100))

def gf2_nonsing(bits,n):
    rows=[0]*n; at=0
    for i in range(n):
        for j in range(i+1,n):
            if (bits>>at)&1:
                rows[i]|=1<<j; rows[j]|=1<<i
            at+=1
    rank=0
    for col in range(n):
        pivot=next((j for j in range(rank,n) if (rows[j]>>col)&1), None)
        if pivot is None:
            continue
        rows[rank],rows[pivot]=rows[pivot],rows[rank]
        for j in range(rank+1,n):
            if (rows[j]>>col)&1:
                rows[j]^=rows[rank]
        rank+=1
    return int(rank==n)

def prime_nonsing(v,n,q):
    a=np.zeros((n,n),dtype=np.int64); r=0
    for i in range(n):
        for j in range(i+1,n):
            a[i,j]=v[r]; a[j,i]=-v[r]%q; r+=1
    rank=0
    for col in range(n):
        pivot=next((j for j in range(rank,n) if a[j,col]%q),None)
        if pivot is None: continue
        a[[rank,pivot]]=a[[pivot,rank]]
        a[rank]=a[rank]*pow(int(a[rank,col]),-1,q)%q
        for j in range(rank+1,n):
            a[j]=(a[j]-a[j,col]*a[rank])%q
        rank+=1
    return int(rank==n)

def diagnostics(counts,q,n,k,exact):
    m=(q**k-1)//(q-1); total=int(sum(counts)); obs=counts/total
    p=nonsing_prob(q,n); pinf=nonsing_prob_inf(q)
    ref=np.array([p**i.bit_count()*(1-p)**(m-i.bit_count()) for i in range(1<<m)])
    refinf=np.array([pinf**i.bit_count()*(1-pinf)**(m-i.bit_count()) for i in range(1<<m)])
    allbits=np.array([[(i>>j)&1 for j in range(m)] for i in range(1<<m)],dtype=float)
    marg=obs@allbits
    cov=(allbits.T*obs)@allbits-np.outer(marg,marg)
    maxcov=max(abs(cov[i,j]) for i in range(m) for j in range(i))
    residuals=(counts-total*ref)/np.sqrt(total*ref*(1-ref))
    return dict(q=q,n=n,k=k,projective_combinations=m,exact=exact,samples=total,
        nonsingular_probability_finite=p,nonsingular_probability_limit=pinf,
        TV_to_independent_finite=float(abs(obs-ref).sum()/2),
        TV_to_independent_limit=float(abs(obs-refinf).sum()/2),
        max_marginal_error=float(abs(marg-p).max()),max_pair_covariance=float(maxcov),
        all_nonsingular_observed=float(obs[-1]),all_nonsingular_independent_finite=float(ref[-1]),
        all_nonsingular_independent_limit=float(refinf[-1]),
        max_pattern_standardized_residual=float(abs(residuals).max()),
        pearson_chisquare=float(((counts-total*ref)**2/(total*ref)).sum()),
        reference_degrees_freedom=(1<<m)-1,
        counts=[int(x) for x in counts])

def exact_small(q,n,k):
    d=n*(n-1)//2; pts=projective_points(q,k); m=len(pts)
    counts=np.zeros(1<<m,dtype=np.int64)
    if q==2:
        ns=np.array([gf2_nonsing(i,n) for i in range(1<<d)],dtype=np.int8)
        for coeffs in itertools.product(range(1<<d),repeat=k):
            mask=0
            for j,t in enumerate(pts):
                v=0
                for a,x in zip(t,coeffs):
                    if a:v^=x
                mask|=int(ns[v])<<j
            counts[mask]+=1
    elif n==4:
        vectors=np.array(list(itertools.product(range(q),repeat=d)),dtype=np.int16)
        # Order 01,02,03,12,13,23: Pf=a01*a23-a02*a13+a03*a12.
        for x in vectors:
            # q^6 possibilities for each second matrix; vectorize.
            z=pts[:,0,None,None]*x[None,None,:]+pts[:,1,None,None]*vectors[None,:,:]
            pf=(z[:,:,0]*z[:,:,5]-z[:,:,1]*z[:,:,4]+z[:,:,2]*z[:,:,3])%q
            masks=((pf!=0).T*(1<<np.arange(m))).sum(axis=1)
            counts+=np.bincount(masks,minlength=1<<m)
    else:
        raise ValueError('unsupported exact run')
    return diagnostics(counts,q,n,k,True)

def sample(q,n,k,samples,rng):
    d=n*(n-1)//2; pts=projective_points(q,k); m=len(pts)
    counts=np.zeros(1<<m,dtype=np.int64)
    for _ in range(samples):
        mask=0
        if q==2:
            # Integer.from_bytes makes independent uniform d-bit vectors.
            coeffs=[int.from_bytes(rng.bytes((d+7)//8),'little')&((1<<d)-1) for _ in range(k)]
            for j,t in enumerate(pts):
                v=0
                for a,x in zip(t,coeffs):
                    if a:v^=x
                mask|=gf2_nonsing(v,n)<<j
        else:
            coeffs=rng.integers(0,q,size=(k,d),dtype=np.int16)
            for j,t in enumerate(pts):
                mask|=prime_nonsing(t@coeffs%q,n,q)<<j
        counts[mask]+=1
    return diagnostics(counts,q,n,k,False)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--samples',type=int,default=20000)
    ap.add_argument('--output',default=str(Path(__file__).resolve().parents[1] / 'data' / 'pencil_checks.json'))
    args=ap.parse_args(); rng=np.random.default_rng(27112026); results=[]
    cases=[('exact',2,2,2),('exact',2,4,2),('exact',2,4,3),('exact',3,4,2),
           ('sample',2,8,2),('sample',2,16,2),('sample',2,32,2),
           ('sample',2,8,3),('sample',2,16,3),('sample',3,8,2),('sample',3,16,2)]
    for typ,q,n,k in cases:
        start=time.monotonic()
        r=exact_small(q,n,k) if typ=='exact' else sample(q,n,k,args.samples,rng)
        r['seconds']=time.monotonic()-start; results.append(r)
        Path(args.output).write_text(json.dumps(dict(seed=27112026,warning='Simulation is evidence only, not proof',results=results),indent=2))
        print(json.dumps({k:v for k,v in r.items() if k!='counts'}),flush=True)
if __name__=='__main__':main()
