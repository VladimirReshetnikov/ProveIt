#!/usr/bin/env python3
"""Exact cyclotomic partial-fraction certificates, standard library only.

All arithmetic is in Q[X]/Phi_L(X). Equality is checked after multiplying
by the ORIGINAL denominator, including repeated poles. This verifier does
not evaluate any polylogarithm or approximate a root of unity.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from math import lcm, gcd
from pathlib import Path
import json

# Scalar polynomials are stored in ascending degree.
def trim(a):
    a=list(a)
    while a and a[-1] == 0: a.pop()
    return a

def add(a,b):
    r=[F(0)]*max(len(a),len(b))
    for j,c in enumerate(a): r[j]+=c
    for j,c in enumerate(b): r[j]+=c
    return trim(r)

def mul(a,b):
    if not a or not b: return []
    r=[F(0)]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b):r[j+k]+=x*y
    return trim(r)

def divrem(a,b):
    a=trim(a);b=trim(b)
    if not b:raise ZeroDivisionError('zero polynomial')
    q=[F(0)]*max(0,len(a)-len(b)+1)
    while a and len(a)>=len(b):
        d=len(a)-len(b); c=F(a[-1])/b[-1];q[d]=c
        for j,x in enumerate(b): a[d+j]-=c*x
        a=trim(a)
    return trim(q),a

@lru_cache(maxsize=None)
def cyclotomic(n):
    p=[F(-1)]+[F(0)]*(n-1)+[F(1)]
    for d in range(1,n):
        if n%d==0:
            p,r=divrem(p,cyclotomic(d));assert not r
    assert all(x.denominator==1 for x in p)
    return tuple(p)

class Field:
    def __init__(self,L):
        self.L=L;self.mod=list(cyclotomic(L));self.d=len(self.mod)-1
        self.zero=(F(0),)*self.d
        self.one=self.scalar(1)
        self.x=self.reduce([0,1])
    def reduce(self,a):
        _,r=divrem(a,self.mod)
        return tuple(r+[F(0)]*(self.d-len(r)))
    def scalar(self,a):return (F(a),)+(F(0),)*(self.d-1)
    def add(self,a,b):return tuple(x+y for x,y in zip(a,b))
    def neg(self,a):return tuple(-x for x in a)
    def sub(self,a,b):return self.add(a,self.neg(b))
    def mul(self,a,b):return self.reduce(mul(a,b))
    def scale(self,a,c):return tuple(F(c)*x for x in a)
    def pow(self,a,n):
        if n<0:return self.pow(self.inv(a),-n)
        ans=self.one
        while n:
            if n&1:ans=self.mul(ans,a)
            a=self.mul(a,a);n//=2
        return ans
    def inv(self,a):
        r0,r1=self.mod,trim(a);t0,t1=[],[F(1)]
        if not r1:raise ZeroDivisionError('zero field element')
        while r1:
            q,r=divrem(r0,r1)
            r0,r1=r1,r
            t0,t1=t1,add(t0,[-x for x in mul(q,t1)])
        assert len(r0)==1
        ans=self.reduce([x/r0[0] for x in t0])
        assert self.mul(a,ans)==self.one
        return ans

def divide_linear(poly,alpha,K):
    """Exact division in K[t] by (1-alpha*t), original constant is 1."""
    q=[poly[0]]
    for j in range(1,len(poly)-1):q.append(K.add(poly[j],K.mul(alpha,q[-1])))
    assert K.add(poly[-1],K.mul(alpha,q[-1]))==K.zero
    return q

def run_case(p,q):
    assert 0<p<q and gcd(p,q)==1
    L=4*lcm(p,q);K=Field(L);ii=K.pow(K.x,L//4)
    P={k for k in range(L) if (p*k-L//4)%L==0}
    Q={k for k in range(L) if (q*k-L//4)%L==0}
    assert len(P)==p and len(Q)==q
    assert len(P&Q)==(1 if (q-p)%4==0 else 0)
    denom=[K.zero]*(p+q+1)
    denom[0]=K.one;denom[p]=K.neg(ii);denom[q]=K.neg(ii)
    denom[p+q]=K.mul(ii,ii)
    target=[K.zero]*(p+q+1);target[p+q]=K.mul(ii,ii)
    result=[K.zero]*(p+q+1);entries=[]
    for k in sorted(P|Q):
        alpha=K.pow(K.x,k)
        if k in P&Q:
            A=K.scalar(F(-(p+q),2*p*q));B=K.scalar(F(1,p*q))
        elif k in P:
            A=K.scale(K.mul(ii,K.inv(K.sub(K.pow(alpha,q),ii))),F(1,p));B=K.zero
        else:
            A=K.scale(K.mul(ii,K.inv(K.sub(K.pow(alpha,p),ii))),F(1,q));B=K.zero
        quotient=divide_linear(denom,alpha,K)
        for j,c in enumerate(quotient):
            result[j+1]=K.add(result[j+1],K.mul(K.mul(A,alpha),c))
        if B!=K.zero:
            quotient2=divide_linear(quotient,alpha,K)
            for j,c in enumerate(quotient2):
                result[j+1]=K.add(result[j+1],K.mul(K.mul(B,alpha),c))
        entries.append({'root_exponent':k,'A':[str(x) for x in A],
                        'B':[str(x) for x in B],'repeated_pole':k in P&Q})
    assert result==target
    return {'p':p,'q':q,'conductor':L,'field_degree':K.d,
            'cyclotomic_polynomial_ascending':[str(x) for x in K.mod],
            'common_root_exponents':sorted(P&Q),'terms':entries,
            'numerator_coefficient_equalities':len(target)*K.d,'status':'PASS'}

def main():
    cases=[run_case(p,q) for p,q in [(1,2),(1,3),(1,5),(2,3),(3,5),(3,7)]]
    out=Path(__file__).resolve().parents[1]/'data'/'cyclotomic_certificates.json'
    out.write_text(json.dumps({'status':'PASS','cases':cases},indent=2)+'\n')
    for c in cases:
        print('PASS p/q={p}/{q}, conductor={conductor}, field degree={field_degree}, repeated roots={common_root_exponents}'.format(**c))
    print('PASS',sum(c['numerator_coefficient_equalities'] for c in cases),'exact rational coordinate equalities')

if __name__=='__main__': main()
