"""Finite independent Fourier/tableau and composition-moment checks.

Adapted from the independent correction audit. Standard library only. No file
reads/writes and no execution at import. This is not an asymptotic proof.
"""
from fractions import Fraction as F
from itertools import permutations
from math import factorial, comb

def check(ok, message):
    if not ok: raise RuntimeError(message)

def comp(n):
    return [(a,b,n-a-b) for a in range(n+1) for b in range(n-a+1)]

def add(a,b): return tuple(x+y for x,y in zip(a,b))

def mul(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            k=add(ka,kb); out[k]=out.get(k,0)+va*vb
    return {k:v for k,v in out.items() if v}

def sign(p): return (-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))

def integral_polynomial(m,p):
    P={c:factorial(m-p)//(factorial(c[0])*factorial(c[1])*factorial(c[2])) for c in comp(m-p)}
    h={c:1 for c in comp(p)}
    alt={p:sign(p) for p in permutations((0,1,2))}
    return mul(mul(P,h),alt)

def partitions(n): return [c for c in comp(n) if c[0]>=c[1]>=c[2]]


def run():
    # Young-lattice branching, no hook-length formula.
    DIM={(0,0,0):1}
    for n in range(1,13):
        for shape in partitions(n):
            total=0
            for j in range(3):
                mu=list(shape);mu[j]-=1;mu=tuple(mu)
                if min(mu)>=0 and mu[0]>=mu[1]>=mu[2]: total+=DIM[mu]
            DIM[shape]=total
    
    def strip(outer,inner):
        if any(inner[j]>outer[j] for j in range(3)): return False
        columns=[c for j in range(3) for c in range(inner[j]+1,outer[j]+1)]
        return len(columns)==len(set(columns))
    
    pairs=0
    for m in range(13):
        poly=[integral_polynomial(m,p) for p in range(m+1)]
        W=[{la:sum(DIM[mu] for mu in partitions(m-p) if strip(la,mu)) for la in partitions(m)} for p in range(m+1)]
        for p in range(m+1):
            for q in range(m+1):
                integral=F(sum(v*poly[q].get(k,0) for k,v in poly[p].items()),6)
                tableau=sum(W[p][la]*W[q][la] for la in partitions(m))
                check(integral==tableau,f'integral mismatch: {(m,p,q)}')
                pairs+=1
    
    # Composition second moments and the exact signed S coefficient identity.
    composition_checks=0
    for p in range(31):
        cs=comp(p);n=len(cs)
        check(F(sum(c[0]*(c[0]-1) for c in cs),n)==F(p*(p-1),6),'composition diagonal')
        check(F(sum(c[0]*c[1] for c in cs),n)==F(p*(p-1),12),'composition off diagonal')
        composition_checks+=2
    
    def d(i):return F(comb(i+2,2),3**i)
    def aa(i):return F(i*(i-1),2)
    s_checks=0
    for t in range(10):
        for i in range(10):
            for j in range(10):
                c=81*d(i+1)*d(j+1)-9*d(i)*d(j)
                b=-81*d(i+1)*d(j+1)*(8+aa(i+1)+aa(j+1))+9*d(i)*d(j)*(4+aa(i)+aa(j))
                target=81*d(i+1)*d(j+1)*(4*t+8-aa(i+1)-aa(j+1))-9*d(i)*d(j)*(4*t+12-aa(i)-aa(j))
                check(4*(t+4)*c+b==target,'S normalization')
                s_checks+=1
    
    return {'status':'PASS','unitary_integral_tableau_pairs':pairs,'all_boundaries_for_m_through':12,'composition_moment_checks':composition_checks,'S_coefficient_checks':s_checks,'asymptotic_proof_from_finite_checks':False}
