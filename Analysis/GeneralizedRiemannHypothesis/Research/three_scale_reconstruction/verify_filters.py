#!/usr/bin/env python3
"""Finite algebraic tests and numerical illustration; not a proof of infinite limits."""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import cos, fsum, isclose, isqrt, log, pi, sqrt
from cmath import exp

SCALES = {2: (1, 0), 3: (0, 1), 6: (1, 1)}

def convolve(a, b):
    c = defaultdict(int)
    for (i,j), x in a.items():
        for (k,l), y in b.items():
            c[i+k,j+l] += x*y
    return {key: v for key,v in c.items() if v}

def filter_terms(i,j,k):
    """Coefficients of A2**(i+2) A3**j A6**k as shifts 2**a * 3**b."""
    d = {(0,0): 1}
    for r, m in zip((2,3,6),(i+2,j,k)):
        a,b = SCALES[r]
        factor = {(0,0): r+1, (a,b): -1, (-a,-b): -r}
        for _ in range(m):
            d = convolve(d,factor)
    return d

def shift_value(a,b):
    return Fraction(2)**a * Fraction(3)**b

def g(r,t):
    return r+1-2*sqrt(r)*cos(t*log(r))

def checks():
    for i,j,k in product(range(4), repeat=3):
        d=filter_terms(i,j,k)
        # Exact cancellation of x and x log x, separating log 2 and log 3.
        assert sum(c*shift_value(a,b) for (a,b),c in d.items()) == 0
        assert sum(c*shift_value(a,b)*a for (a,b),c in d.items()) == 0
        assert sum(c*shift_value(a,b)*b for (a,b),c in d.items()) == 0
        assert all(abs(a)<=i+2+k and abs(b)<=j+k for a,b in d)
    print('PASS: exact leading-term cancellation and shift support for 64 filters.')
    for i,j,k in product(range(2),repeat=3):
        for t in (0, 1.7, 14.134725, 41.3):
            d=filter_terms(i,j,k)
            z=sum(c*exp((0.5+1j*t)*(a*log(2)+b*log(3))) for (a,b),c in d.items())
            expected=g(2,t)**(i+2)*g(3,t)**j*g(6,t)**k
            assert abs(z-expected)<1e-8*max(1,abs(expected))
    print('PASS: numerical critical-line multiplier checks (32 cases).')
    a,b=log(2),log(3)
    t,tp=pi*(2/b-1/a),pi*(2/b+1/a)
    assert 0<t<tp
    assert isclose(g(2,t),g(2,tp),abs_tol=1e-12)
    assert isclose(g(3,t),g(3,tp),abs_tol=1e-12)
    assert abs(g(6,t)-g(6,tp))>1e-4
    print(f'PASS: two-scale collision t={t:.12f}, t_prime={tp:.12f}; third-scale gap={abs(g(6,t)-g(6,tp)):.12f}.')
    nodes=[(1,2,3),(2,3,4),(4,5,6)]
    masses=[Fraction(3,7),Fraction(1,4),Fraction(5,9)]
    target=nodes[1]; previous=sum(masses)
    for n in range(1,9):
        def q(u):
            out=Fraction(1)
            for r,x,y in zip((2,3,6),u,target):
                out *= (1-Fraction((x-y)**2,16*r))**n
            return out
        value=sum(m*q(u) for m,u in zip(masses,nodes))
        assert masses[1]<=value<=previous
        previous=value
    print('PASS: exact rational localizer monotonicity on a finite toy measure.')

def prime_power_prefix(queries):
    """Compute P(x)=sum Lambda(m)(x/m-1) for integer queries, q=1."""
    limit=max(queries)
    sieve=bytearray([1])*(limit+1)
    sieve[:2]=bytes(2)
    for p in range(2,isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
    powers=[]
    for p in range(2,limit+1):
        if sieve[p]:
            m=p; lp=log(p)
            while m<=limit:
                powers.append((m,lp)); m*=p
    powers.sort()
    results={}; i=0; chunks_a=[]; chunks_b=[]
    for x in sorted(queries):
        j=i
        while j<len(powers) and powers[j][0]<=x: j+=1
        chunks_a.append(fsum(lp/m for m,lp in powers[i:j]))
        chunks_b.append(fsum(lp for m,lp in powers[i:j]))
        results[x]=x*fsum(chunks_a)-fsum(chunks_b)
        i=j
    return results

def prime_demo():
    specs=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
    ns=range(3,7)
    terms={spec:filter_terms(*spec) for spec in specs}
    queries=set()
    for n in ns:
        for d in terms.values():
            for a,b in d:
                assert n+a>=0 and n+b>=0
                queries.add(2**(n+a)*3**(n+b))
    values=prime_power_prefix(queries)
    print(f'\nIllustrative floating-point values, q=1, largest prime-sum argument {max(queries)}:')
    print(' n        x             M000 sample     M100 sample     M010 sample     M001 sample')
    for n in ns:
        x=6**n; row=[]
        for spec in specs:
            z=fsum(c*values[2**(n+a)*3**(n+b)] for (a,b),c in terms[spec].items())/sqrt(x)
            row.append(z)
        print(f'{n:2d} {x:9d} '+ ' '.join(f'{z:15.9f}' for z in row))
    print('Samples can be negative. They are not limsups or certified error bounds.')

if __name__=='__main__':
    checks()
    prime_demo()
