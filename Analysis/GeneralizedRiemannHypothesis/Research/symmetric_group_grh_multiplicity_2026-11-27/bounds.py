#!/usr/bin/env python3
"""Compute the new uniform bound and the old reflection bound.
The recurrence for B is integral. The CSV and table use floats for illustration.
Use exact_bound(n) for a rational result.
"""
from fractions import Fraction as F
import csv
from pathlib import Path


def largest_prime_factors(n):
    pmax = [0]*(n+1)
    for p in range(2,n+1):
        if not pmax[p]:
            for k in range(p,n+1,p):
                pmax[k] = p
    return pmax


def exact_bound(n):
    assert n>=2
    p=largest_prime_factors(n)
    B=[0]*(n+1)
    for k in range(2,n+1):
        B[k]=k+B[k//p[k]]
    return sum((F(B[k],k) for k in range(2,n+1)),F(0))


def compute(degrees):
    n=max(degrees)
    p=largest_prime_factors(n)
    B=[0]*(n+1)
    # For very large n, repeated rational accumulation is expensive.
    # Accumulate in floating point only for descriptive large-n data.
    C=old=S=0.0
    for k in range(2,n+1):
        B[k]=k+B[k//p[k]]
        assert k<=B[k]<=2*(k-1)
        C+=B[k]/k
        old+=2*(k-1)/k
        S+=1/p[k]
        if k in degrees:
            yield (k,k-1,C,old,C/(k-1),S)

if __name__=='__main__':
    rows=list(compute({3,12,13,14,15,16,25,50,100,1000,10000,100000,1000000}))
    with Path(__file__).with_name('bounds.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','conjectured_optimal','uniform_bound','old_reflection_bound','ratio_to_optimal','sum_reciprocal_largest_prime']);w.writerows(rows)
    for r in rows:
        print(f'{r[0]:>7}: {r[2]:.6f} vs {r[3]:.6f}, ratio {r[4]:.6f}')
