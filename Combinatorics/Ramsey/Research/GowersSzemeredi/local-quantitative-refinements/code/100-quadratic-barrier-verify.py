#!/usr/bin/env python3
"""Exact finite checks and optional high-precision tests for the accompanying paper.

Default checks use only Python's standard library. --numerical also needs
NumPy and mpmath. These checks supplement, and do not replace, the proofs.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
import json
from math import comb, gcd
from pathlib import Path


def rank_mod(rows: list[list[int]], p: int) -> int:
    a = [[x % p for x in row] for row in rows]
    if not a: return 0
    r = 0
    for col in range(len(a[0])):
        pivot = next((j for j in range(r, len(a)) if a[j][col]), None)
        if pivot is None: continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][col], -1, p)
        a[r] = [(x * inv) % p for x in a[r]]
        for j in range(len(a)):
            if j != r:
                scale = a[j][col]
                a[j] = [(x - scale*y) % p for x, y in zip(a[j], a[r])]
        r += 1
        if r == len(a): break
    return r


def cube_rows(d: int) -> list[list[int]]:
    return [[1] + [(v >> j) & 1 for j in range(d)] for v in range(1 << d)]


def rectangles(d: int) -> list[tuple[int, ...]]:
    rows = cube_rows(d)
    buckets: dict[tuple[int, ...], list[tuple[int, int]]] = defaultdict(list)
    for a, b in combinations(range(1 << d), 2):
        buckets[tuple(x+y for x,y in zip(rows[a], rows[b]))].append((a,b))
    ans = set()
    for pairs in buckets.values():
        for left, right in combinations(pairs, 2):
            block = tuple(sorted(left + right))
            if len(set(block)) == 4: ans.add(block)
    return sorted(ans)


def partition_count(d: int) -> int:
    incidence = [[] for _ in range(1 << d)]
    for block in rectangles(d):
        mask = sum(1 << v for v in block)
        for v in block: incidence[v].append(mask)
    @lru_cache(None)
    def rec(mask: int) -> int:
        if not mask: return 1
        v = (mask & -mask).bit_length()-1
        return sum(rec(mask ^ block) for block in incidence[v] if block & mask == block)
    return rec((1 << (1 << d))-1)


def raw_spike_moment(rows: list[list[int]], p: int) -> Fraction:
    """Moment of product (p*1_{L=0}-1); exact rank expansion, no floating point."""
    total = Fraction()
    m = len(rows)
    for mask in range(1 << m):
        subset = [row for j,row in enumerate(rows) if mask & (1 << j)]
        exponent = len(subset)-rank_mod(subset,p)
        total += (-1)**(m-len(subset)) * p**exponent
    return total


def circle_moment(rows: list[list[int]], R: int = 2) -> Fraction:
    """For R=2, h(t)=cos(2πt)+cos(4πt), every nonzero Fourier coefficient is 1/2."""
    if R != 2: raise ValueError('This exact rational helper is for R=2.')
    frequencies = (-2,-1,1,2)
    count = 0
    for xi in product(frequencies, repeat=len(rows)):
        if all(sum(x * row[c] for x,row in zip(xi,rows)) == 0 for c in range(len(rows[0]))):
            count += 1
    return Fraction(count, 2**len(rows))


def exact_checks() -> dict:
    counts = defaultdict(int)
    cube_data = []
    for d in (2,3,4):
        rows = cube_rows(d)
        rect = set(rectangles(d))
        expected = (6**d-2*4**d+2**d)//8
        assert len(rect) == expected
        for p in (5,7):
            for size in (2,3,4):
                for subset in combinations(range(1 << d),size):
                    rank = rank_mod([rows[v] for v in subset],p)
                    assert rank == (3 if size == 4 and subset in rect else size)
                    counts['finite_field_rank_checks'] += 1
        for subset in combinations(range(1 << d),4):
            moment = circle_moment([rows[v] for v in subset])
            assert moment == (Fraction(1,4) if subset in rect else 0)
            counts['circle_fourth_moment_checks'] += 1
        value = partition_count(d)
        assert value == {2:1,3:6,4:635}[d]
        cube_data.append({'d':d,'vertices':1<<d,'four_circuits':expected,'partitions':value})
    for p,k in ((5,4),(7,6),(11,8)):
        rows = [[1,j] for j in range(k)]
        for i,j,l in combinations(range(k),3):
            assert raw_spike_moment([rows[i],rows[j],rows[l]],p) == p-1
            counts['spike_progression_triples'] += 1
    for d in (2,3):
        rows = cube_rows(d); rect = set(rectangles(d))
        for size in (2,3,4):
            for subset in combinations(range(1 << d),size):
                moment = raw_spike_moment([rows[v] for v in subset],5)
                assert moment == (4 if size == 4 and subset in rect else 0)
                counts['spike_cube_moment_checks'] += 1
    arithmetic_data = []
    for k in range(3,11):
        triples = list(combinations(range(k),3))
        total = Fraction()
        for i,j,l in triples:
            val = circle_moment([[1,i],[1,j],[1,l]])
            assert val == (Fraction(1,4) if i+l == 2*j else 0)
            total += val
            counts['circle_progression_triples'] += 1
        Dk = (k-1)**2//4
        assert total == Fraction(Dk,4)
        K = sum((Fraction(gcd(j-i,l-j),l-i) for i,j,l in triples),Fraction())
        arithmetic_data.append({'k':k,'D_k':Dk,'K_k':str(K)})
    for bound,n in ((1,3),(2,3),(3,3),(2,4)):
        base=2*bound+1
        for vector in product(range(-bound,bound+1),repeat=n):
            val=sum(c*base**j for j,c in enumerate(vector))
            assert (val == 0) == all(c == 0 for c in vector)
            assert 2*abs(val) <= base**n-1
            counts['signed_radix_checks'] += 1
    return {'status':'PASS','checks':dict(counts),'total_checks':sum(counts.values()),
            'cube_constants':cube_data,'arithmetic_constants':arithmetic_data}


def characteristic_groups(rows: list[list[int]], p: int) -> tuple[dict,int]:
    import numpy as np
    r = len(rows[0]); m=len(rows)
    parameters=np.array(list(product(range(p),repeat=r)),dtype=np.int16)
    zeros=(np.asarray(rows,dtype=np.int16) @ parameters.T % p == 0).astype(np.int16)
    groups=defaultdict(int)
    for sigma_tuple in product((-1,0,1),repeat=m):
        sigma=np.array(sigma_tuple,dtype=np.int16)
        values=sigma @ zeros
        hist=tuple(int(x) for x in np.bincount(values+m,minlength=2*m+1))
        nonzero=sum(x != 0 for x in sigma_tuple)
        sign=(-1)**sum(x == -1 for x in sigma_tuple)
        groups[(hist,sum(sigma_tuple),nonzero)] += sign
    return {key:val for key,val in groups.items() if val},p**r


def numerical_checks() -> dict:
    import mpmath as mp
    mp.mp.dps=90
    p=5; delta=mp.mpf('0.5'); lam=mp.mpf('0.125')
    cube_groups,cube_den=characteristic_groups(cube_rows(3),p)
    ap_groups,ap_den=characteristic_groups([[1,j] for j in range(4)],p)
    a=mp.exp(-mp.mpf('0.5')); theta=lam*a
    def evaluate(groups,den,m,n,constant,amplitude):
        scale=1/mp.sqrt(n*(p-1))
        exponentials={r:mp.exp(1j*p*r*scale) for r in range(-m,m+1)}
        phases={r:mp.exp(-1j*r*scale) for r in range(-m,m+1)}
        total=mp.mpc(0)
        for (hist,s,nonzero),multiplicity in groups.items():
            psi=phases[s]*sum(hist[r+m]*exponentials[r] for r in range(-m,m+1))/den
            coeff=multiplicity*(amplitude/(2j))**nonzero*constant**(m-nonzero)
            total += coeff*psi**n
        assert abs(mp.im(total)) < mp.mpf('1e-70')
        return mp.re(total)
    results=[]
    for n in (16,64,256,1024,4096):
        scale=1/mp.sqrt(n*(p-1))
        single=(mp.exp(1j*(p-1)*scale)+(p-1)*mp.exp(-1j*scale))/p
        mean=mp.im(single**n)
        cube=evaluate(cube_groups,cube_den,8,n,-mean,mp.mpf(1))
        ap=evaluate(ap_groups,ap_den,4,n,delta-lam*mean,lam)
        cube_prediction=6*a**8/(p-1)**2/n**2
        ap_prediction=4*delta*theta**3/mp.sqrt(p-1)/mp.sqrt(n)
        assert cube > 0
        results.append({'n':n,'cube_to_leading_term':mp.nstr(cube/cube_prediction,22),
                        'progression_to_leading_term':mp.nstr((ap-delta**4)/ap_prediction,22),
                        'mean_centering':mp.nstr(mean,22)})
    assert abs(mp.mpf(results[-1]['cube_to_leading_term'])-1)<mp.mpf('0.03')
    assert abs(mp.mpf(results[-1]['progression_to_leading_term'])-1)<mp.mpf('0.03')
    return {'status':'PASS','precision_decimal_digits':90,
            'method':'finite characteristic-function sums; no Monte Carlo',
            'cube_group_count':len(cube_groups),'ap_group_count':len(ap_groups),'results':results}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--numerical',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result={'exact':exact_checks()}
    if args.numerical: result['numerical']=numerical_checks()
    text=json.dumps(result,indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text+'\n',encoding='utf-8')
    print(text)

if __name__=='__main__': main()
