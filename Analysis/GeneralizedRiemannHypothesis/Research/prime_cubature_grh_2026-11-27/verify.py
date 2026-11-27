#!/usr/bin/env python3
"""Independent exact verifier: Python standard library only."""
import json, math, itertools
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def isprime(p):
    return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))

def verify_certificate():
    data=json.loads((ROOT/'certificate.json').read_text())
    q,k,X=data['q'],data['k'],data['X'];dels=set(data['deleted'])
    assert len(set(q))==len(q) and all(t>2 and isprime(t) for t in q)
    assert 1<=k<=len(q) and X>=2
    A=[s for j in range(k+1) for s in itertools.combinations(range(len(q)),j)]
    c=list(map(Fraction,data['coefficients'])); assert len(c)==len(A)
    pool=[p for p in range(X+1,2*X) if isprime(p) and p not in q]
    assert dels<=set(pool) and len(dels)==len(data['deleted'])
    w=lambda p:(p-X)**2*(2*X-p)**2
    survivors=[p for p in pool if p not in dels];Z=sum(map(w,survivors))
    assert len(pool)==data['count'] and len(survivors)==data['survivors']
    sums=[Fraction(0)]*len(A);ratios=[]
    for p in survivors:
        raw=[pow(t,(p-1)//2,p) for t in q]; assert all(x in (1,p-1) for x in raw)
        u=[1 if x==1 else -1 for x in raw]
        v=[math.prod(u[i] for i in s) for s in A]
        ratio=sum(x*y for x,y in zip(v,c)); ratios.append(ratio)
        assert Fraction(3,4)<=ratio<=Fraction(5,4)
        mass=Fraction(w(p),Z)*ratio
        for j,x in enumerate(v):sums[j]+=mass*x
    assert sums==[1]+[0]*(len(A)-1)
    lost=Fraction(sum(map(w,dels)),sum(map(w,pool)));assert lost<=Fraction(2,100)
    print(f'PASS: {len(A)} exact moment equations on {len(survivors)} of {len(pool)} primes')
    print(f'deleted mass={float(lost):.8f}, ratio range=[{float(min(ratios)):.8f}, {float(max(ratios)):.8f}]')

def layer_moment(r,s,j):
    plus=(r+s)//2;minus=r-plus
    return Fraction(sum((-1)**l*math.comb(minus,l)*math.comb(plus,j-l)
                        for l in range(j+1)),math.comb(r,j))

def verify_sharpness():
    cases=0
    for r in range(7,102,2):
        for a in range(3,r+1,2):
            if a*a<6*r:continue
            lam=Fraction(r-1,a*a-1)
            alpha=(lam-(1-lam)/a)/2;beta=(lam+(1-lam)/a)/2
            assert min(alpha,beta,1-lam)>=0 and alpha+beta+1-lam==1
            m=[(1-lam)*layer_moment(r,1,j)+alpha*layer_moment(r,a,j)+beta*layer_moment(r,-a,j) for j in range(1,5)]
            assert m==[0,0,Fraction(r-a*a,r*(r-1)*(r-2)),Fraction(a*a-3*r,r*(r-2)*(r-3))]
            assert lam/2<=beta<=lam
            cases+=1
    print(f'PASS: exact layer-moment formulas in {cases} parameter cases')

if __name__=='__main__':
    verify_certificate();verify_sharpness()
