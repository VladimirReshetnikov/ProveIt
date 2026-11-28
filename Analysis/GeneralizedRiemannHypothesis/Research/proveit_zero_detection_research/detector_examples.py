#!/usr/bin/env python3
"""Exact block-code and Frobenius-weight calculations; standard library only."""
from math import comb, factorial, prod
from fractions import Fraction
from itertools import product
from collections import Counter


def multiply(a,b):
    result=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            result[i+j]+=x*y
    return result


def example(n,p,brute=False):
    r=n//p
    d=r.bit_length()
    blocks=[2**j for j in range(d-1)]
    blocks.append(r-sum(blocks))
    A,B=[1],[1]
    for b in blocks:
        A=multiply(A,[1]+[0]*(b-1)+[p-1])
        numer=[comb(b,h)*((p-1)**h+(p-1)*(-1)**h) for h in range(b+1)]
        assert all(x%p==0 for x in numer)
        B=multiply(B,[x//p for x in numer])
    order=p**(r-d)
    assert all(x>0 for x in A) and sum(A)==p**d
    assert all(x>=0 for x in B) and sum(B)==order
    assert len(A)==len(B)==r+1
    C=max(Fraction(comb(r,h)*(p-1)**h,A[h]) for h in range(r+1))
    weights={h:Fraction(p**h*factorial(h)*factorial(n-p*h)*B[h],order)
             for h in range(r+1) if B[h]}
    assert all(x.denominator==1 for x in weights.values())
    assert sum(x/Fraction(p**h*factorial(h)*factorial(n-p*h)) for h,x in weights.items())==1
    if brute:
        actual_A=Counter(sum(b for b,x in zip(blocks,v) if x) for v in product(range(p),repeat=d))
        actual_B=Counter()
        for v in product(range(p),repeat=r):
            offset=0
            keep=True
            for b in blocks:
                if sum(v[offset:offset+b])%p:
                    keep=False
                    break
                offset+=b
            if keep:
                actual_B[sum(x!=0 for x in v)]+=1
        assert all(actual_A[h]==A[h] and actual_B[h]==B[h] for h in range(r+1))
    return blocks, order, C, weights, B

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run without -O')
    for p in (2,3,5):
        for r in range(1,8 if p<5 else 6):
            example(p*r+1,p,brute=True)
    print('PASS: weight enumerators and mean-one Frobenius weights; direct enumeration for p=2,3,5 in small ranks.')
    print('Ternary constructions:')
    for n in (12,15,30,60,300):
        blocks, order,C,weights,B=example(n,3)
        print(f'n={n}: blocks={blocks}, |H|={order}, C(D)={C}, support={len(weights)} classes')
        if n==15:
            print(f'  H-weight enumerator coefficients: {B}')
            print(f'  Frobenius weights (indexed by h): {weights}')
