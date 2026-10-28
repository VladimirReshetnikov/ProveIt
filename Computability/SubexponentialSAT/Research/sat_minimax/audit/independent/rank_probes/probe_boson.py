#!/usr/bin/env python3
"""Small exact-modular probes of Appendix B crossing-piece flattenings.

Source: anthropics/formal-math@1a6eee293b9e00cb432eef6018a21f523623a9af,
eth/paper.pdf Appendix B, especially (O2), equations (53)--(56).

The external basis is all partitions of h, not the first 2**lambda basis
vectors used in the SAT construction. b_mu=t_mu replaces the source's
(h!/z_mu)*t_mu, a nonzero external diagonal rescaling modulo 1009 for
1 <= h <= 7. It does not change either flattening rank. This program is
an exploratory finite-size calculation, not a rank theorem or SAT solver.
Requires numpy. Use --central for h=7 to avoid a much larger full probe.
"""
from functools import lru_cache
from math import comb
import numpy as np,time,json,sys
P=1009
@lru_cache(None)
def parts(n,lo=1):
    if n==0:return ((),)
    return tuple((k,)+q for k in range(lo,n+1) for q in parts(n-k,k))
def rm(t,k):
    z=list(t);z.remove(k);return tuple(z)
def choose(n,k):
    return comb(n,k) if n>=k>=0 else ((-1)**k*comb(k-n-1,k) if n<0 and k>=0 else 0)
@lru_cache(None)
def op(a,tgt,src):
    if not a:return int(tgt==src)
    n,tail=a[0],a[1:]
    return (sum(choose(l-1,n-1)*op(tail,rm(tgt,l),src) for l in set(tgt))+
            sum(choose(-k-1,n-1)*k*src.count(k)*op(tail,tgt,rm(src,k)) for k in set(src)))%P
# weight shift is intrinsically sum(tgt)-sum(src), and r argument therefore omitted.
@lru_cache(None)
def afam(mu):
    c={():1}
    for n in mu:
        d={}
        for a,v in c.items():
            for j in range(1,n+1):
                key=tuple(sorted(a+(j,)))
                d[key]=(d.get(key,0)+v*((-1)**(n-1))*comb(n,j))%P
        c=d
    return tuple(c.items())
def rank(A):
    A=A.copy()%P;m,n=A.shape;r=0
    for j in range(n):
        idx=np.nonzero(A[r:,j])[0]
        if not len(idx):continue
        k=r+int(idx[0]);A[[r,k]]=A[[k,r]]
        A[r]=(A[r]*pow(int(A[r,j]),-1,P))%P
        if r+1<m:A[r+1:]=(A[r+1:]-A[r+1:,j,None]*A[r,None,:])%P
        r+=1
        if r==m:break
    return r

def probe(h,central_only=False):
    if not 1<=h<=7:raise ValueError("certified int64-safe probe range is 1 <= h <= 7")
    base=parts(h);N=len(base);ats=[afam(a) for a in base]
    amons=sorted(set(a for ats0 in ats for a,v in ats0));start=time.time()
    # Q' form, intermediate k=s+i. Left(x,y,tau)=a_x<i>[s-h+i] y; Right(u,v,tau)=b_v[h-s-i] tau.
    B={};A={}
    for k in range((2 if central_only else 4)*h+1):
        mid=parts(k)
        B[k]=np.array([[op(v,u,tau) for tau in mid] for u in base for v in base],dtype=np.int64)
        A[k]=np.array([[op(a,tau,y) for tau in mid] for a in amons for y in base],dtype=np.int64).reshape(len(amons),N,len(mid))
        print('prepared',h,k,len(mid),round(time.time()-start,2),op.cache_info(),file=sys.stderr,flush=True)
    rows=[];total=np.zeros((N*N,N*N),dtype=np.int64)
    for s in ([0] if central_only else range(-2*h,2*h+1)):
        T=np.zeros((N*N,N*N),dtype=np.int64)
        for i in range(2*h+1):
            k=s+i
            if k<0 or k>4*h:continue
            Cs=np.array([[dict(aa).get(a,0)*choose(sum(a)+h,i) for a in amons] for aa in ats],dtype=np.int64)%P
            L=(Cs@A[k].reshape(len(amons),-1))%P
            L=L.reshape(N*N,-1)
            T=(T+((-1)**i)*(L@B[k].T))%P
        total=(total+T)%P
        if h<=3:
            Q=np.zeros((N*N,N*N),dtype=np.int64)
            for i in range(2*h+1):
                k=2*h-s-i
                if k<0 or k>4*h:continue
                mid=parts(k)
                for xi,aa in enumerate(ats):
                    for yi,y in enumerate(base):
                        for ui,u in enumerate(base):
                            for vi,v in enumerate(base):
                                Q[xi*N+yi,ui*N+vi]=(Q[xi*N+yi,ui*N+vi]+((-1)**i)*sum(sum(c*choose(sum(a)+h,i)*op(a,u,tau) for a,c in aa)*op(v,tau,y) for tau in mid))%P
            if not np.array_equal(T,Q):raise ValueError(('two orders mismatch',h,s))
        rr=rank(T);cc=rank(T.reshape(N,N,N,N).transpose(0,2,1,3).reshape(N*N,N*N))
        rows.append({'h':h,'s':s,'N':N,'row_rank':rr,'col_rank':cc,'row_bound':min(N*N,sum(len(parts(s+i)) for i in range(2*h+1) if s+i>=0)),'col_bound':min(N*N,sum(len(parts(2*h-s-i)) for i in range(2*h+1) if 2*h-s-i>=0))})
        print(rows[-1],flush=True)
    expected=np.zeros_like(total)
    from math import factorial,prod
    for xi,x in enumerate(base):
        z=prod(k**x.count(k)*factorial(x.count(k)) for k in set(x))
        for yi,y in enumerate(base):expected[xi*N+yi,yi*N+xi]=z%P
    if central_only:
        print('CENTRAL PROBE ONLY: full crossing sum not tested',h,file=sys.stderr)
    else:
        if not np.array_equal(total,expected):raise ValueError(('crossing reconstruction failed',h))
        print('CROSSING RECONSTRUCTION PASSED',h,file=sys.stderr)
    return rows
if __name__=='__main__':
    import argparse
    from pathlib import Path
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('h',type=int)
    ap.add_argument('--central',action='store_true')
    ap.add_argument('--output',required=True)
    args=ap.parse_args()
    R=probe(args.h,args.central)
    Path(args.output).write_text(json.dumps(R,indent=2)+'\n')
