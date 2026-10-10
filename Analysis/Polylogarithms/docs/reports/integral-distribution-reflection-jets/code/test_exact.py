#!/usr/bin/env python3
"""Exact regression battery; standard library only. No numerical period tests."""
from __future__ import annotations
from itertools import product, combinations
from math import prod
from pathlib import Path
import json
import platform
import time
from distribution import Distribution, Poly, factor, phi, active_count, rank_binary

ROOT = Path(__file__).resolve().parents[1]
if not __debug__:
    raise RuntimeError('Run without -O: the regression suite uses assertions.')


def eval_char2(poly: Poly, values: tuple[int, ...], multiply) -> int:
    out = 0
    for monomial, coefficient in poly.terms:
        if coefficient & 1:
            term = 1
            for value, exponent in zip(values, monomial):
                for _ in range(exponent):
                    term = multiply(term, value)
            out ^= term
    return out


def binary_reflection_rank(d: Distribution, weights: tuple[int, ...]) -> int:
    columns = []
    for a in d.basis:
        col = 1 << d.index[a]
        for b, c in d.normal_form(-a % d.q).items():
            if c.evaluate(weights) & 1:
                col ^= 1 << d.index[b]
        columns.append(col)
    return rank_binary(columns)


def gf4_mul(a: int, b: int) -> int:
    ans = 0
    while b:
        if b & 1:
            ans ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7  # X^2 + X + 1
    return ans


def field_rank(columns: list[list[int]], add, mul, inv) -> int:
    pivots = {}
    for column in columns:
        a = list(column)
        while any(a):
            k = max(i for i, v in enumerate(a) if v)
            if k not in pivots:
                z = inv(a[k])
                pivots[k] = [mul(v, z) for v in a]
                break
            z = a[k]
            a = [add(x, mul(z, y)) for x, y in zip(a, pivots[k])]
    return len(pivots)


def gf4_reflection_rank(d: Distribution, weights: tuple[int, ...]) -> int:
    columns = []
    for a in d.basis:
        col = [0] * len(d.basis)
        col[d.index[a]] = 1
        for b, c in d.normal_form(-a % d.q).items():
            col[d.index[b]] ^= eval_char2(c, weights, gf4_mul)
        columns.append(col)
    return field_rank(columns, lambda a,b:a^b, gf4_mul, lambda a:gf4_mul(a,a))


def series_mul(a: int, b: int, length: int) -> int:
    ans = 0
    while b:
        if b & 1:
            ans ^= a
        a <<= 1
        b >>= 1
    return ans & ((1 << length) - 1)


def jet_cokernel_dimension(d: Distribution, weights: tuple[int, ...], length: int) -> int:
    mul = lambda a,b:series_mul(a,b,length)
    columns = []
    mask = (1 << length) - 1
    for a in d.basis:
        coeffs = {b:eval_char2(c, weights, mul)
                  for b,c in d.normal_form(-a % d.q).items()}
        coeffs[a] = coeffs.get(a,0) ^ 1
        for j in range(length):
            col = 0
            for b, value in coeffs.items():
                col ^= ((value << j) & mask) << (length * d.index[b])
            columns.append(col)
    return len(d.basis)*length-rank_binary(columns)


def valuation(a: int, cap: int) -> int:
    return (a & -a).bit_length()-1 if a else cap


def chain_test(q: int, modulus: int) -> dict:
    """Check d^2=0 and exactness in positive degrees over F_modulus."""
    ps = tuple(p for p,_ in factor(q))
    weights = {p:(p+q+1)%modulus for p in ps}
    groups = []
    for j in range(len(ps)+1):
        groups.append([(S,x) for S in combinations(ps,j)
                       for x in range(0,q,prod(S))])
    maps = [None]
    ranks = []
    for j in range(1,len(groups)):
        index = {key:i for i,key in enumerate(groups[j-1])}
        columns = []
        for S,x in groups[j]:
            out = [0]*len(index)
            for i,p in enumerate(S):
                T = tuple(t for t in S if t!=p)
                sign = (-1)**i
                for y in range(0,q,prod(T)):
                    if p*y%q == x:
                        out[index[(T,y)]] += sign
                out[index[(T,x)]] -= sign*weights[p]
            columns.append([v%modulus for v in out])
        maps.append(columns)
        rank = field_rank(columns,lambda a,b:(a-b)%modulus,
                          lambda a,b:a*b%modulus,
                          lambda a:pow(a,-1,modulus))
        ranks.append(rank)
    for j in range(2,len(groups)):
        for col in maps[j]:
            residual = [0]*len(groups[j-2])
            for c, previous in zip(col,maps[j-1]):
                for i,v in enumerate(previous):
                    residual[i] = (residual[i]+c*v)%modulus
            assert not any(residual), ('d_squared',q,modulus,j)
    padded = [0]+ranks+[0]
    for j in range(1,len(groups)):
        assert padded[j]+padded[j+1]==len(groups[j]), ('chain_exactness',q,modulus,j)
    assert len(groups[0])-padded[1]==phi(q)
    return {'level':q,'field_characteristic':modulus,
            'chain_dimensions':[len(g) for g in groups], 'boundary_ranks':ranks}


def main():
    start = time.monotonic()
    counts = {'universal_levels':0,'raw_polynomial_rows':0,'unit_minor_checks':0,
              'support_degree_checks':0,'binary_reflection_specializations':0,
              'gf4_reflection_specializations':0,'jet_cases':0,'resolution_cases':0}
    extra = {}
    for q in list(range(1,121))+[150,180,210]:
        d = Distribution(q)
        assert len(d.basis)==phi(q)
        d.check_unit_minor()
        counts['universal_levels']+=1
        counts['unit_minor_checks']+=1
        for p,x,row in d.rows():
            assert not d.reduce_vector(row), ('raw_row',q,p,x)
            counts['raw_polynomial_rows']+=1
        for a in range(q):
            m = d.conductor(a)
            for b,c in d.normal_form(a).items():
                n = d.conductor(b)
                assert m%n==0
                f = dict(factor(m//n))
                assert all(all(e<=f.get(p,0) for p,e in zip(d.primes,mon))
                           for mon,coef in c.terms)
                counts['support_degree_checks']+=1
        if q>2:
            r = active_count(q)
            h = 2**(r-1)
            for values in product((0,1),repeat=len(d.primes)):
                exceptional = all(v==1 for p,v in zip(d.primes,values) if p!=2)
                target = len(d.basis)//2-(h if exceptional else 0)
                assert binary_reflection_rank(d,values)==target, ('binary',q,values)
                counts['binary_reflection_specializations']+=1
    for q in [3,4,6,8,9,10,12,15,20,24,30,60]:
        d = Distribution(q)
        r = active_count(q); h=2**(r-1)
        for values in product(range(4),repeat=len(d.primes)):
            w = dict(zip(d.primes,values))
            exceptional = all(w[p]==1 for p in d.primes if p!=2)
            if q%4==0:
                exceptional &= w[2] in (0,1)
            target = len(d.basis)//2-(h if exceptional else 0)
            assert gf4_reflection_rank(d,values)==target, ('gf4',q,values)
            counts['gf4_reflection_specializations']+=1
    jets = []
    for q in [4,8,9,12,15,20,24,30,45,60,105]:
        d = Distribution(q)
        n=len(d.basis)//2; h=2**(active_count(q)-1)
        for profile in range(5):
            for length in range(1,8):
                values=[]
                for i,p in enumerate(d.primes):
                    # Includes generic points, unequal contacts, the other 2-branch,
                    # and a curve wholly contained in the exceptional locus.
                    if profile==0: val=1
                    elif profile==1: val=1^(1<<(i+1))
                    elif profile==2: val=1^(1<<(i+3))
                    elif profile==3: val=(1<<2) if p==2 else 1^(1<<4)
                    else: val=0 if p!=2 else 1
                    values.append(val&((1<<length)-1))
                w=dict(zip(d.primes,values))
                scalars=[w[p]^1 for p in d.primes if p!=2]
                if q%4==0:
                    scalars.append(series_mul(w[2],w[2]^1,length))
                contact=min(valuation(a,length) for a in scalars)
                predicted=n*length+h*contact
                observed=jet_cokernel_dimension(d,tuple(values),length)
                assert observed==predicted, ('jet',q,profile,length,observed,predicted)
                counts['jet_cases']+=1
                if q in (12,15,60) and profile in (1,2,3):
                    jets.append({'level':q,'profile':profile,'length':length,
                                 'weight_bit_polynomials':values,'contact_capped':contact,
                                 'observed_dimension':observed,'predicted_dimension':predicted})
    chains=[]
    for q in list(range(2,41))+[60,105]:
        for ell in (2,3,5):
            chains.append(chain_test(q,ell))
            counts['resolution_cases']+=1
    extra['jet_examples']=jets
    extra['resolution_examples']=[r for r in chains if r['level'] in (12,15,30,60,105)]
    result={'status':'PASS','arithmetic':'exact integer polynomials and finite fields',
            'counts':counts,'python':platform.python_version(),
            'elapsed_seconds':round(time.monotonic()-start,3),**extra}
    (ROOT/'logs/exact_tests.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if not k.endswith('examples')},indent=2))

if __name__=='__main__':
    main()
