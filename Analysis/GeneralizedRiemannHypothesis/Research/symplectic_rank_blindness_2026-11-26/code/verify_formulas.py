#!/usr/bin/env python3
"""Exact finite-field projection laws and certified limiting constants.

All finite laws use integers/Fraction. The formulas apply to every prime
power q. Exhaustive field arithmetic is a separate independent check.
Run from any directory: python3 code/verify_formulas.py
"""
from fractions import Fraction as F
from functools import lru_cache
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from pathlib import Path
import csv
import json

ROOT = Path(__file__).resolve().parents[1]

def prod(values):
    value = F(1)
    for x in values:
        value *= x
    return value

@lru_cache(None)
def a(q, j):
    return prod(1-F(1, q**i) for i in range(1, j+1))

@lru_cache(None)
def gaussian(q, n, k):
    if k < 0 or k > n:
        return 0
    value = prod(F(q**(n-i)-1, q**(k-i)-1) for i in range(k))
    assert value.denominator == 1
    return value.numerator

@lru_cache(None)
def isotropic_subspaces(q, s, l):
    """Number of l-subspaces in a nondegenerate alternating 2s-space."""
    if l < 0 or l > s:
        return 0
    value = prod(F(q**(2*(s-i))-1, q**(l-i)-1) for i in range(l))
    assert value.denominator == 1
    return value.numerator

def kernel_types(q, n, s, k, t):
    d, l = n-2*s, k-t
    if not (0 <= t <= min(k, d) and 0 <= l <= s):
        return 0
    return gaussian(q, d, t)*q**((d-t)*l)*isotropic_subspaces(q, s, l)

def uniform_nullity(q, n, k):
    if not 0 <= k <= n:
        return F(0)
    return F(1, q**(k*k))*a(q,n)**2/(a(q,k)**2*a(q,n-k))

def normalization(q, n, s):
    return prod(1-F(1, q**(2*j)) for j in range(s+1,n+1))

def density(q, n, s, k, t):
    return q**(k*(k-1)//2)*prod(1-F(1,q**j) for j in range(k-t+1,k+1))/normalization(q,n,s)

def exact_laws(q, n, s):
    assert q >= 2 and 0 <= 2*s <= n
    uniform = [uniform_nullity(q,n,k) for k in range(n+1)]
    projection = [F(0) for _ in range(n+1)]
    overlap = F(0)
    support_mass = F(0)
    for k in range(n+1):
        for t in range(k+1):
            cnt = kernel_types(q,n,s,k,t)
            if not cnt:
                continue
            w = uniform[k]*F(cnt,gaussian(q,n,k))
            likelihood = density(q,n,s,k,t)
            projection[k] += w*likelihood
            overlap += w*min(F(1),likelihood)
            support_mass += w
    assert sum(uniform) == sum(projection) == 1
    full_tv = 1-overlap
    rank_tv = sum(abs(x-y) for x,y in zip(projection,uniform))/2
    assert 0 <= rank_tv <= full_tv <= 1
    # Geometry gives this first moment for every form type, independently.
    assert sum(q**k*projection[k] for k in range(n+1)) == F(2*q**n,q**n+1)
    if 2*s == n:
        expected = (uniform[0]+uniform[1])*(1/normalization(q,n,s)-1)
        assert rank_tv == expected
        assert full_tv == 1-support_mass
        for k in range(n+1):
            if k <= 1:
                assert projection[k] > uniform[k]
            else:
                assert projection[k] < uniform[k]
    return uniform, projection, full_tv, rank_tv

def decimal(x, digits=45, rounding=ROUND_FLOOR):
    with localcontext() as ctx:
        ctx.prec = digits
        ctx.rounding = rounding
        return str(Decimal(x.numerator)/Decimal(x.denominator))

def delta_interval(q, M=140, K=12):
    """Rational enclosure using a product tail and a Gaussian series tail."""
    assert M >= K and q >= 2
    upper_product = a(q,M)
    lower_product = upper_product*(1-F(1,q**M*(q-1)))
    assert lower_product > 0
    partial = sum((F(1,q**(k*k))*(1-F(1,q**(k*(k-1)//2)))/a(q,k)**2 for k in range(2,K+1)),F(0))
    tail = F(1,q**((K+1)**2))/(lower_product*(1-F(1,q**(2*K+3))))
    lower = lower_product*partial
    upper = upper_product*partial+tail
    return lower,upper

def main():
    out = ROOT/'results'
    out.mkdir(exist_ok=True)
    rows=[]
    count=0
    # Tests cover degenerate/nondegenerate forms and characteristic two.
    for q in [2,3,4,5,8,9]:
        for n in range(1,13):
            for s in range(n//2+1):
                exact_laws(q,n,s)
                count += 1
    for q in [2,3,4,5]:
        for n in [2,4,6,8,12,16,20,24,32]:
            u,p,full,rank=exact_laws(q,n,n//2)
            rows.append(dict(q=q,n=n,full_tv=decimal(full),rank_tv=decimal(rank),
                             rank_tv_times_qn=decimal(rank*q**n),
                             full_tv_exact=str(full),rank_tv_exact=str(rank)))
    with (out/'nondegenerate_distances.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
    type_rows=[]
    for s in range(7):
        u,p,full,rank=exact_laws(2,12,s)
        type_rows.append(dict(q=2,n=12,s=s,radical_dimension=12-2*s,
                              full_tv=decimal(full),rank_tv=decimal(rank)))
    with (out/'form_type_distances.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=type_rows[0].keys());writer.writeheader();writer.writerows(type_rows)
    intervals={}
    for q in [2,3,4,5,7,8,9]:
        lo,hi=delta_interval(q)
        intervals[str(q)]={'lower':decimal(lo,42,ROUND_FLOOR),
                           'upper':decimal(hi,42,ROUND_CEILING),
                           'rational_interval_width_upper':decimal(hi-lo,8,ROUND_CEILING),
                           'rounding_note':'Displayed endpoints are outward-rounded; the rational interval is narrower.',
                           'product_cutoff':140,'series_cutoff':12}
    (out/'certified_constants.json').write_text(json.dumps(intervals,indent=2)+'\n')
    summary={'exact_parameter_cases':count,'passed':True,
             'identities':['normalization','first kernel moment','data processing',
                           'nondegenerate exact rank TV','nondegenerate exact support TV',
                           'nondegenerate rank sign classification'],
             'independent_enumeration':'See exhaustive_check.json; not derived from these formulas.'}
    (out/'formula_checks.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    print(json.dumps(intervals,indent=2))
    print('Binary finite dimensions:')
    for row in rows:
        if row['q']==2:
            print(row['n'], row['full_tv'][:18],row['rank_tv'][:18])

if __name__=='__main__':
    main()
