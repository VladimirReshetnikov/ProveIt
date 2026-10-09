"""Small exact rational matrix/polynomial routines for reproducible checks.

These routines prioritize transparency over speed. No floating point is used.
Polynomial coefficients are stored in increasing powers of eta.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from itertools import product, permutations
from typing import Iterable

Matrix = tuple[tuple[F, ...], ...]
Poly = tuple[Matrix, ...]

def matrix(rows: Iterable[Iterable[int | F]]) -> Matrix:
    a = tuple(tuple(F(x) for x in row) for row in rows)
    if not a or any(len(row) != len(a) for row in a):
        raise ValueError("Expected a nonempty square matrix")
    return a

def zeros(d: int) -> Matrix:
    return tuple(tuple(F(0) for _ in range(d)) for _ in range(d))

def eye(d: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(d)) for i in range(d))

def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(x+y for x,y in zip(ar,br)) for ar,br in zip(a,b))

def scale(a: Matrix, c: int | F) -> Matrix:
    return tuple(tuple(c*x for x in row) for row in a)

def sub(a: Matrix,b: Matrix) -> Matrix:
    return add(a,scale(b,-1))

def mul(a: Matrix,b: Matrix) -> Matrix:
    d=len(a)
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(d) if a[i][k] and b[k][j]),F(0)) for j in range(d)) for i in range(d))

def transpose(a: Matrix) -> Matrix:
    return tuple(zip(*a))

def mean(mats: Iterable[Matrix]) -> Matrix:
    mats=tuple(mats)
    if not mats: raise ValueError("Empty mean")
    result=zeros(len(mats[0]))
    for a in mats: result=add(result,a)
    return scale(result,F(1,len(mats)))

def sandwich_poly(p: Poly,h: Matrix,a: F,degree: int) -> Poly:
    """Coefficients of (I-eta*a*h) p(eta) (I-eta*a*h)."""
    z=zeros(len(h)); out=[]
    for k in range(degree+1):
        q=p[k] if k<len(p) else z
        if 0<=k-1<len(p):
            q=sub(q,scale(add(mul(h,p[k-1]),mul(p[k-1],h)),a))
        if 0<=k-2<len(p):
            q=add(q,scale(mul(mul(h,p[k-2]),h),a*a))
        out.append(q)
    return tuple(out)

def average_poly(ps: Iterable[Poly]) -> Poly:
    ps=tuple(ps)
    return tuple(mean(p[k] for p in ps) for k in range(len(ps[0])))

def expectations(hs: tuple[Matrix,...], weights: tuple[F,...], degree: int=4,
                 metric: Matrix | None=None) -> tuple[Poly,Poly]:
    """Return (with_replacement, without_replacement) Gram polynomials.

    Sampling without replacement means a uniformly random ordered tuple of
    distinct indices. Position j always has the fixed weight weights[j].
    Subset dynamic programming is for verification only; its cost is exponential.
    """
    n=len(hs);m=len(weights);d=len(hs[0])
    if not 1<=m<=n: raise ValueError("Require 1 <= block length <= number of components")
    if any(len(h)!=d or transpose(h)!=h for h in hs):
        raise ValueError("All Hessians must be symmetric and of equal dimension")
    if any(a<=0 for a in weights): raise ValueError("Weights must be positive")
    g=eye(d) if metric is None else metric
    base=(g,)+tuple(zeros(d) for _ in range(degree))
    wr=base
    for a in reversed(weights):
        wr=average_poly(sandwich_poly(wr,h,a,degree) for h in hs)
    @lru_cache(None)
    def rr(used: int) -> Poly:
        j=used.bit_count()
        if j==m: return base
        return average_poly(sandwich_poly(rr(used|(1<<i)),h,weights[j],degree)
                            for i,h in enumerate(hs) if not used&(1<<i))
    return wr,rr(0)

def direct_expectations(hs: tuple[Matrix,...],weights: tuple[F,...],degree: int=4,
                        metric: Matrix | None=None) -> tuple[Poly,Poly]:
    """Independent enumeration using product coefficients, not sandwiches."""
    n=len(hs);m=len(weights);d=len(hs[0]);z=zeros(d)
    g=eye(d) if metric is None else metric
    def path(indices):
        p=[eye(d)]
        for i,a in zip(indices,weights):
            nxt=[z for _ in range(min(degree,len(p))+1)]
            for k,pk in enumerate(p):
                nxt[k]=add(nxt[k],pk)
                if k+1<=degree: nxt[k+1]=sub(nxt[k+1],scale(mul(hs[i],pk),a))
            p=nxt
        out=[]
        for k in range(degree+1):
            out.append(sum_mats(mul(mul(transpose(p[j]),g),p[k-j])
                       for j in range(len(p)) if 0<=k-j<len(p)))
        return tuple(out)
    def sum_mats(ms):
        out=z
        for a in ms: out=add(out,a)
        return out
    return (average_poly(path(idx) for idx in product(range(n),repeat=m)),
            average_poly(path(idx) for idx in permutations(range(n),m)))

def moments(hs: tuple[Matrix,...]) -> tuple[Matrix,Matrix,tuple[Matrix,...]]:
    h=mean(hs); ds=tuple(sub(a,h) for a in hs)
    v=mean(mul(d,d) for d in ds)
    return h,v,ds

def schedule_constants(weights: tuple[F,...],n: int) -> dict[str,F]:
    if not 2<=len(weights)<=n or any(a<=0 for a in weights):
        raise ValueError("Require 2 <= m <= n and strictly positive weights")
    e=[F(1),F(0),F(0),F(0),F(0)]
    prefix=F(0);ws=[]
    for a in weights:
        for k in range(4,0,-1): e[k]+=a*e[k-1]
        ws.append(a*prefix);prefix+=a
    t=sum((a*w for a,w in zip(weights,ws)),F(0))
    b0=2*e[3]+2*e[1]*e[2]-t
    a0=2*e[4]+2*e[1]*e[3]+e[2]**2-sum(w*w for w in ws)
    c=4*e[2]/(n-1); b=b0/(n-1); a=a0/(n-1)
    gamma=b*b/c-a
    return dict(c=c,b=b,a=a,gamma=gamma,t=b/c,e2=e[2],discriminant=b0*b0-4*e[2]*a0)

def evaluate(p: Poly,eta: F) -> Matrix:
    out=zeros(len(p[0]))
    for coeff in reversed(p): out=add(scale(out,eta),coeff)
    return out

def quadratic(a: Matrix,x: tuple[F,...]) -> F:
    return sum((x[i]*a[i][j]*x[j] for i in range(len(x)) for j in range(len(x))),F(0))
