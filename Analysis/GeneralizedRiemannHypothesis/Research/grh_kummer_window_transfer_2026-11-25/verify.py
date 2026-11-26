#!/usr/bin/env python3
"""Finite sanity checks for report.tex; no numerical L-function or RH claims."""
from fractions import Fraction
from math import isqrt, log, ceil, prod
from collections import Counter
from itertools import product


def primes(n):
    sieve = bytearray(b'\1') * (n + 1)
    sieve[:2] = b'\0\0'
    for p in range(2, isqrt(n)+1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b'\0' * ((n-p*p)//p+1)
    return [p for p in range(2,n+1) if sieve[p]]


def affine_values(l):
    for a in range(1,l):
        for b in range(l):
            v = sum((a*x+b-x)%l==0 for x in range(l))-1
            g = int(a==1 and b==0)
            I = int(a==1)
            f = I-g
            assert l*g == I+v
            assert l*f == (l-1)*I-v
            yield a,b,v


def affine_check(l):
    vals=list(affine_values(l)); n=l*(l-1)
    assert len(vals)==n
    assert Counter(v for _,_,v in vals)==Counter({l-1:1,-1:l-1,0:l*(l-2)})
    assert sum(v for _,_,v in vals)==0
    assert sum(v*v for _,_,v in vals)==n
    for a in range(1,l):
        assert sum(v for a0,_,v in vals if a0==a)==0
    return n


def prime_check(ls, limit):
    ps=primes(limit); checks=0; counts={}
    for l in ls:
        c=Counter()
        for p in ps:
            if p in (2,l): continue
            I=int((p-1)%l==0)
            g=int(bool(I) and pow(2,(p-1)//l,p)==1)
            # Independent direct root count: use exhaustive modular evaluation.
            r=sum(pow(a,l,p)==2%p for a in range(p))
            assert l*g==I+r-1
            assert l*(I-g)==(l-1)*I-(r-1)
            c['split']+=g; c['nonresidue']+=I-g; c['other']+=1-I
            checks+=1
        counts[l]=dict(c)
    return checks,counts


def block_check(ls, bs):
    # Exact expectation and variance in the product group, independent of
    # periodic congruences. Test also every conditional multiplicative fiber.
    groups=[list(affine_values(l)) for l in ls]
    total=0; s1=Fraction(); s2=Fraction(); fibres={}
    for t in product(*groups):
        v=sum((b*g[2] for b,g in zip(bs,t)),Fraction())
        total+=1; s1+=v; s2+=v*v
        key=tuple(g[0] for g in t)
        fibres[key]=fibres.get(key,Fraction())+v
    assert s1==0 and s2/total==sum(b*b for b in bs)
    assert all(v==0 for v in fibres.values())
    return total,s2/total,len(fibres)


def window_example(R,kappa,lam):
    # Illustrative analytic radius; not a certified radius for any L-function.
    c=ceil(max((kappa+lam+1)/log(R/3),(kappa+lam+5)/log(2)))+1
    C=ceil(max(1,kappa+lam+1+c*log(3)))+1
    rates=(c*log(R/3),c*log(2)-4,C-c*log(3))
    assert min(rates)>kappa+lam
    return c,C,rates


if __name__=='__main__':
    ls=[3,5,7,11,13,17,19]
    print('Exact affine checks:')
    for l in ls: print(f'  ell={l:2d}, group size={affine_check(l):3d}')
    checks,counts=prime_check(ls,3000)
    print(f'Root-count checks over p <= 3000: {checks}')
    for l,c in counts.items(): print(f'  ell={l}: {c}')
    n,var,fib=block_check([3,5,7],[Fraction(1),Fraction(3,2),Fraction(2)])
    print(f'Exact product group: {n} tuples, {fib} fibers, variance={var}')
    print('Illustrative gamma-window constants, kappa=2, lambda=1:')
    for R in [3.01,3.1,3.5,4.0]:
        c,C,rates=window_example(R,2,1)
        print(f'  R={R}: c={c}, C0={C}, decay rates={tuple(round(x,6) for x in rates)}')
    ps=primes(100000)
    A=prod(1-1/(l*(l-1)) for l in ps)
    print(f'Artin constant partial product to 100000 (floating point illustration): {A:.10f}')
    print('All finite assertions passed. Analytic proofs and open covolume comparison are not machine-verified.')
