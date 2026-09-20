#!/usr/bin/env python3
"""Exact symbolic lattice-point and magic polynomials; Python standard library only.

Polynomials are stored as exponent tuples mapped to integers.  In dimension n,
all coefficients are scaled by n!.  No interpolation or numerical tolerances.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, factorial
from pathlib import Path
import json
import time

Poly = dict[tuple[int, ...], int]

@lru_cache(None)
def power_sum(k: int) -> tuple[Fraction, ...]:
    """Coefficients of sum_{r=1}^m r^k, from the telescoping identity."""
    q = [Fraction(0) for _ in range(k + 2)]
    for j in range(1, k + 2):
        q[j] = Fraction(comb(k + 1, j))
    for h in range(k):
        for j, c in enumerate(power_sum(h)):
            q[j] -= comb(k + 1, h) * c
    return tuple(c / (k + 1) for c in q)

@lru_cache(None)
def kernel(a: int, b: int, scale: int) -> tuple[tuple[tuple[int, int, int], int], ...]:
    """scale * sum_{r=1}^Y (X+Y-r)^a (Z+r)^b."""
    out = defaultdict(int)
    for i in range(a + 1):
        for j in range(a - i + 1):
            h = a - i - j
            first = comb(a, i) * comb(a - i, j) * (-1)**h
            for z in range(b + 1):
                c = first * comb(b, z)
                for p, f in enumerate(power_sum(h + b - z)):
                    if f:
                        v = scale * f
                        if v.denominator != 1:
                            raise ArithmeticError('Insufficient integer scale')
                        out[(i, j + p, z)] += c * v.numerator
    return tuple((e, c) for e, c in sorted(out.items()) if c)


def next_lattice(prev: Poly, n: int) -> Poly:
    """Return n! L_n from (n-1)! L_{n-1} using the slice recurrence."""
    den = factorial(n)
    out = defaultdict(int)
    for e, c in prev.items():
        # First block: b1 L_{n-1}(b1+b2,b3,...,bn).
        for j in range(e[0] + 1):
            target = (j + 1, e[0] - j) + e[1:]
            out[target] += n * den * c * comb(e[0], j)
        # Middle blocks: replacing two adjacent entries by a kernel in three.
        for i in range(n - 2):
            for (u,v,w), k in kernel(e[i], e[i + 1], den):
                target = e[:i] + (u,v,w) + e[i + 2:]
                out[target] += n * c * k
        # Final block: only the last old entry is split.
        for (u,v,w), k in kernel(e[-1], 0, den):
            assert w == 0
            out[e[:-1] + (u,v)] += n * c * k
    ans = {}
    for e,c in out.items():
        q,r = divmod(c,den)
        if r:
            raise ArithmeticError('Nonintegral scaled polynomial')
        if q:
            ans[e] = q
    return ans


def magic_polynomials(lattice: Poly, n: int) -> list[Poly]:
    """n! mu_i(1+x1,...,1+xn) for i=0,...,n."""
    # First get n! L_n(1+q1,q2,...,qn).  A degree-d monomial contributes t^d.
    homogeneous = defaultdict(int)
    for e,c in lattice.items():
        for p in range(e[0] + 1):
            homogeneous[(p,) + e[1:]] += c * comb(e[0],p)
    out = [defaultdict(int) for _ in range(n + 1)]
    for e,c in homogeneous.items():
        if not c:
            continue
        d = sum(e)
        weights = [(i, (-1)**(i-d) * comb(n-d, i-d)) for i in range(d,n+1)]
        # q1=x1 and qj=1+xj for j>=2.
        for tail in product(*(range(a+1) for a in e[1:])):
            a = (e[0],) + tail
            v = c
            for h,p in zip(e[1:],tail):
                v *= comb(h,p)
            for i,w in weights:
                out[i][a] += v*w
    return [{e:c for e,c in p.items() if c} for p in out]


def evaluate(poly: Poly, values: tuple[int,...]) -> int:
    result = 0
    for e,c in poly.items():
        term = c
        for x,a in zip(values,e):
            term *= x**a
        result += term
    return result


def save_poly(poly: Poly, path: Path, n: int) -> None:
    data = {'dimension':n, 'scale':factorial(n),
            'terms':[[list(e),c] for e,c in sorted(poly.items())]}
    path.write_text(json.dumps(data, separators=(',',':'))+'\n')


def read_poly(path: Path) -> Poly:
    """Read a canonical certificate, rejecting malformed or duplicate terms."""
    data = json.loads(path.read_text())
    n = data.get('dimension')
    if type(n) is not int or n < 1 or data.get('scale') != factorial(n):
        raise ValueError(f'Invalid dimension or scale in {path}')
    result: Poly = {}
    previous = None
    for exponents, coefficient in data['terms']:
        e = tuple(exponents)
        if (len(e) != n or any(type(a) is not int or a < 0 for a in e)
                or type(coefficient) is not int or coefficient == 0
                or (previous is not None and e <= previous)):
            raise ValueError(f'Invalid or unsorted term in {path}')
        result[e] = coefficient
        previous = e
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-dimension', type=int, default=10)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'data'/'certificates')
    args = parser.parse_args()
    if not 1 <= args.max_dimension <= 14:
        parser.error('Choose a maximum dimension in 1..14 (large cases are expensive).')
    args.output.mkdir(parents=True,exist_ok=True)
    P = {(1,):1}
    summary=[]
    for n in range(1,args.max_dimension+1):
        begin=time.monotonic()
        if n>1:
            P=next_lattice(P,n)
        save_poly(P,args.output/f'lattice_{n:02d}.json',n)
        print(f'n={n} lattice_terms={len(P)} lattice_seconds={time.monotonic()-begin:.3f}',flush=True)
        M=magic_polynomials(P,n)
        record={'dimension':n,'lattice_terms':len(P),'magic':[]}
        for i,pol in enumerate(M):
            save_poly(pol,args.output/f'magic_{n:02d}_{i:02d}.json',n)
            neg=[(e,c) for e,c in pol.items() if c<0]
            info={'index':i, 'terms':len(pol),'negative_terms':len(neg),
                  'constant_scaled':pol.get((0,)*n,0),
                  'minimum_nonzero_scaled_coefficient':min(pol.values()) if pol else None}
            record['magic'].append(info)
            print(f' n={n} mu={i} terms={len(pol)} negative={len(neg)}',flush=True)
            if neg:
                print('  first_negative',sorted(neg)[:3],flush=True)
        record['seconds']=time.monotonic()-begin
        summary.append(record)
        (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
        print(f'n={n} TOTAL_SECONDS={record["seconds"]:.3f}',flush=True)

if __name__=='__main__':
    main()
