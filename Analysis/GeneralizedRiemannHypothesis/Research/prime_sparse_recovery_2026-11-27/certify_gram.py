#!/usr/bin/env python3
"""Exact rational/integer certificate of coherence <= 61/1000 for sample_primes.txt.
No floating-point arithmetic is used. Requires numpy, sympy. NumPy int64
matrix products are proved not to overflow by an explicit bound below.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial,lcm
from pathlib import Path
import numpy as np
from sympy import factorint, primitive_root, totient, isprime, mobius, divisors

Q=31
S=10**6
TARGET=F(61,1000)

# Machin's identity: pi = 16 arctan(1/5) - 4 arctan(1/239).
# Alternating-series brackets with rational endpoints.
def atan_bracket(n):
    a=sum((F((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(20)),F(0))
    b=a+F(1,41*n**41)
    return a,b
l5,u5=atan_bracket(5); l239,u239=atan_bracket(239)
pi_lo=16*l5-4*u239; pi_hi=16*u5-4*l239
PI=F(3141592653589793,10**15)
assert PI-F(1,10**15)<pi_lo<pi_hi<PI+F(1,10**15)
# Taylor degree 40; |angle|<7, derivatives of sine/cosine <=1.
component_error=F(2,10**15)+F(7**41,factorial(41))
assert component_error < F(1,2*S)

@lru_cache(None)
def rounded_root(phase):
    phase=phase%1
    x=2*PI*phase
    assert 0<=x<7
    term=F(1); re=F(1); im=F(0)
    for j in range(1,41):
        term=term*x/j
        if j%4==0: re+=term
        if j%4==1: im+=term
        if j%4==2: re-=term
        if j%4==3: im-=term
    a,b=round(S*re),round(S*im)
    # Rounding + Taylor/angle error < 1/S in each component.
    assert abs(a)<=S+1 and abs(b)<=S+1
    return a,b

# Each local table contains exact rational phases, or None at nonunits.
def local(p,a):
    q=p**a
    if p==2 and a==1: return []
    if p==2 and a==2: return [[None,F(0),None,F(1,2)]]
    ret=[]
    if p==2:
        n=2**(a-2)
        for b in range(2):
            for j in range(1,n,2):
                v=[None]*q
                for h in range(n):
                    u=pow(5,h,q); phase=F(j*h,n)
                    v[u]=phase%1; v[-u%q]=(phase+F(b,2))%1
                ret.append(v)
    else:
        n=int(totient(q)); g=int(primitive_root(q))
        for j in range(1,n):
            if a>1 and j%p==0: continue
            v=[None]*q
            for h in range(n): v[pow(g,h,q)]=F(j*h,n)%1
            ret.append(v)
    return ret


def tables():
    yield 1,[F(0)]
    for q in range(2,Q+1):
        fac=[(int(p),int(a)) for p,a in factorint(q).items()]
        for locs in product(*(local(p,a) for p,a in fac)):
            tab=[]
            for n in range(q):
                phases=[v[n%(p**a)] for (p,a),v in zip(fac,locs)]
                tab.append(None if None in phases else sum(phases,F(0))%1)
            yield q,tab


def main():
    primes=[int(s) for s in Path(__file__).with_name('sample_primes.txt').read_text().split()]
    m=len(primes)
    assert m==len(set(primes)) and all(40000<=p<=80000 and isprime(p) for p in primes)
    columns=list(tables()); D=len(columns)
    expected=sum(int(sum(mobius(q//d)*totient(d) for d in divisors(q))) for q in range(1,Q+1))
    assert D==expected==197
    X=np.empty((m,D),dtype=np.int64); Y=X.copy()
    for j,(q,tab) in enumerate(columns):
        approx=[(0,0) if phase is None else rounded_root(phase) for phase in tab]
        for i,p in enumerate(primes): X[i,j],Y[i,j]=approx[p%q]
    # Worst bound on every intermediate integer Gram entry, including diagonal correction.
    assert 2*m*(S+1)**2+m*S*S < 2**63
    R=X.T@X+Y.T@Y-m*S*S*np.eye(D,dtype=np.int64)
    I=X.T@Y-Y.T@X
    max_sq=max(int(r)**2+int(i)**2 for r,i in zip(R.flat,I.flat))
    # If every entry differs from its rational approximation by complex modulus <=2/S,
    # the product error is at most 4/S + 4/S**2. Averaging does not enlarge it.
    allowance=TARGET-F(4,S)-F(4,S*S)
    assert allowance>0
    assert F(max_sq,(m*S*S)**2)<=allowance**2
    print(f'Exact certificate passed: m={m}, D={D}, coherence <= {TARGET}.')
    print(f'max squared integer Gram numerator = {max_sq}')
    print(f'Gram denominator = {m*S*S}')
    print(f'product approximation allowance = {F(4,S)+F(4,S*S)}')
    # k=2, e=61, t=91: exact lower bound on the recovery margin.
    margin=1-4*TARGET-F(4*(61+2*91),m)
    assert margin>0
    print(f'Exact certified margin for e=61,t=91,k=2: {margin}>0.')

if __name__=='__main__': main()
