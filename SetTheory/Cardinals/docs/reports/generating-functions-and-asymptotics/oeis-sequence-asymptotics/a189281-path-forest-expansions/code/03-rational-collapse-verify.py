#!/usr/bin/env python3
"""Exact checks and coefficient generation for directed-offset rational collapse.

Python standard library only. No recurrence conjecture and no fitted constants.
Run: python code/verify.py --order 100 --identity-order 16
The finite checks do not replace the arbitrary-order proofs in the article.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import json
import time

Poly = tuple[int, ...]  # ascending powers


def trim(a: list[int] | tuple[int, ...]) -> Poly:
    b = list(a)
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    return tuple(b or [0])


def add(a: Poly, b: Poly, scale: int = 1) -> Poly:
    out = list(a) + [0] * max(0, len(b)-len(a))
    for i, v in enumerate(b):
        out[i] += scale*v
    return trim(out)


def mul(a: Poly, b: Poly) -> Poly:
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


@lru_cache(None)
def fallpoly(shift: int, length: int) -> Poly:
    """Polynomial (n-shift) falling length."""
    out = (1,)
    for i in range(length):
        out = mul(out, (-shift-i, 1))
    return out


def fall(n: int, k: int) -> int:
    out = 1
    for i in range(k):
        out *= n-i
    return out


def rise(n: int, k: int) -> int:
    out = 1
    for i in range(k):
        out *= n+i
    return out


def gbinom(n: int, k: int) -> int:
    """Generalized integer binomial, including negative upper index."""
    if k < 0:
        return 0
    if n >= 0:
        return comb(n, k) if k <= n else 0
    return (-1)**k*comb(k-n-1, k)


@lru_cache(None)
def partitions(n: int, largest: int | None = None) -> tuple[tuple[int, ...], ...]:
    if n == 0:
        return ((),)
    top = min(n, largest if largest is not None else n)
    return tuple((j,)+rest for j in range(top, 0, -1)
                 for rest in partitions(n-j, j))


def automorphism(parts: tuple[int, ...]) -> int:
    out = 1
    for c in Counter(parts).values():
        out *= factorial(c)
    return out


@lru_cache(None)
def forest_poly(r: int, edges: tuple[int, ...]) -> Poly:
    """Stable F_r, independently from the profile formula in the article."""
    k, c = sum(edges), len(edges)
    E: Poly = (1,)
    for d in edges:
        E = mul(E, (1, d))
    out = (0,)
    for h, eh in enumerate(E):
        out = add(out, fallpoly(k+h, c-h), (-1)**h*rise(r-1, h)*eh)
    return out


def profile_R_numerator(H: int, r: int, s: int) -> Poly:
    """Return H! n^(fall 2H) R_H via profile partitions; all integers."""
    out = (0,)
    for k in range(H+1):
        for parts in partitions(k):
            c, v = len(parts), k+len(parts)
            weight = factorial(H)//(factorial(H-k)*automorphism(parts))
            term = mul(mul(forest_poly(r, parts), forest_poly(s, parts)),
                       fallpoly(v, 2*H-v))
            out = add(out, term, (-1)**(H-k)*weight)
    return out


def a_weight(j: int, r: int, s: int) -> int:
    return rise(r-1, j)*rise(s-1, j)//factorial(j)


def closed_R_numerator(H: int, r: int, s: int) -> Poly:
    out = (0,)
    for j in range(H+1):
        weight = a_weight(j, r, s)*gbinom(H-r-s, H-j)
        out = add(out, fallpoly(H+j, H-j), factorial(H)*weight)
    return out


def stable_mu(n: int, k: int, r: int, s: int) -> Fraction:
    """Single-sum moment; valid when all position/value paths have >= k vertices."""
    if n < 0 or k < 0 or r < 1 or s < 1:
        raise ValueError('Use n,k >= 0 and r,s >= 1.')
    if n < 2*k:
        raise ValueError('Single-sum evaluation requires n >= 2*k.')
    total = sum(a_weight(j, r, s)*factorial(n-k-j)*
                gbinom(n-r-s+1-j, k-j) for j in range(k+1))
    return Fraction(total, factorial(n))


@lru_cache(None)
def one_path(L: int) -> dict[tuple[int, ...], int]:
    return {parts: factorial(len(parts))//automorphism(parts)
            for parts in partitions(L)}


@lru_cache(None)
def tilings(n: int, r: int) -> dict[tuple[int, ...], int]:
    out: dict[tuple[int, ...], int] = {(): 1}
    for i in range(r):
        L = (n+r-1-i)//r
        nxt: dict[tuple[int, ...], int] = defaultdict(int)
        for a, ca in out.items():
            for b, cb in one_path(L).items():
                nxt[tuple(sorted(a+b, reverse=True))] += ca*cb
        out = dict(nxt)
    return out


def moment_numerators(n: int, r: int, s: int) -> list[int]:
    """Exact n!*E binom(X,k) from full finite path tilings (no stability)."""
    left, right = tilings(n,r), tilings(n,s)
    out = [0]*(n+1)
    for parts, count in left.items():
        out[n-len(parts)] += count*right.get(parts,0)*automorphism(parts)
    return out


def exact_histogram(n: int, r: int, s: int) -> list[int]:
    moments = moment_numerators(n,r,s)
    return [sum((-1)**(k-q)*comb(k,q)*moments[k] for k in range(q,n+1))
            for q in range(n+1)]


def correction_polynomials(order: int, r: int, s: int) -> list[list[int]]:
    """B_J(u), coefficient lists. O(order^3) integer arithmetic operations."""
    if order < 0 or r < 1 or s < 1:
        raise ValueError('Order must be nonnegative and offsets positive.')
    S = [[0]*(order+1) for _ in range(order+1)]
    S[0][0] = 1
    for n in range(1,order+1):
        for k in range(1,n+1):
            S[n][k] = S[n-1][k-1]+k*S[n-1][k]
    B = [[1]]
    for J in range(1,order+1):
        row = [0]*(J+1)
        for h in range(1,J+1):
            row[h] = sum(a_weight(j,r,s)*gbinom(h-r-s,h-j)*S[J-1][h+j-1]
                         for j in range(min(h,J-h)+1))
        B.append(list(trim(row)))
    return B


def factorial_coefficients(order: int, r: int, s: int) -> list[int]:
    return [sum(a_weight(j,r,s)*gbinom(m-j-r-s,m-2*j)*(-1)**(m-j)
                for j in range(m//2+1)) for m in range(order+1)]


def run(order: int, identity_order: int, outdir: Path) -> dict:
    started = time.monotonic()
    log: list[str] = []
    def report(text: str) -> None:
        print(text, flush=True); log.append(text)
    pairs = [(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(3,3),(4,4)]
    count = 0
    for r,s in pairs:
        for H in range(identity_order+1):
            assert profile_R_numerator(H,r,s) == closed_R_numerator(H,r,s), (H,r,s)
            count += 1
    report(f'PASS: {count} exact polynomial identities from independent profile sums; '
           f'h=0..{identity_order}, 9 offset pairs.')
    for H in range(4, identity_order+1):
        expected = tuple(24*factorial(H)*v for v in fallpoly(H-1,H-4))
        assert closed_R_numerator(H,2,2) == expected
    report(f'PASS: A189281 rational-collapse polynomial identity for h=4..{identity_order}.')
    nchecks = mchecks = 0
    for n in range(9):
        brute = {(r,s): [0]*(n+1) for r in range(1,4) for s in range(1,4)}
        for perm in permutations(range(n)):
            for r in range(1,4):
                differences = Counter(perm[i+r]-perm[i] for i in range(max(0,n-r)))
                for s in range(1,4):
                    brute[r,s][differences[s]] += 1
        for (r,s),hist in brute.items():
            assert exact_histogram(n,r,s) == hist
            nchecks += 1
            for k in range(min(n//max(r,s),n//2)+1):
                actual = Fraction(sum(comb(q,k)*v for q,v in enumerate(hist)),factorial(n))
                assert stable_mu(n,k,r,s)==actual, (n,k,r,s)
                mchecks += 1
    report(f'PASS: {nchecks} full-histogram comparisons against brute permutations n=0..8.')
    report(f'PASS: {mchecks} single-sum moment comparisons in their stability ranges.')
    datafile = outdir/'b189281_0_30.txt'
    oeis_checked = 0
    if datafile.exists():
        for line in datafile.read_text().splitlines():
            if not line or line.startswith('#'):
                continue
            n,value = map(int,line.split())
            assert exact_histogram(n,2,2)[0] == value, n
            oeis_checked += 1
        report(f'PASS: {oeis_checked} OEIS A189281 values using independent finite tilings.')
    B = correction_polynomials(order,2,2)
    c = [sum((-1)**h*v for h,v in enumerate(row)) for row in B]
    assert c[:17] == [1,3,2,1,0,3,26,101,124,-1409,-13266,-59103,-9448,
                      2525459,26632378,152270749,106221948]
    d = factorial_coefficients(order,2,2)
    for n in range(6,order+1):
        # Derived from x^3(1+x)D' + (2+3x+3x^2-2x^3)D = (x+2)(x+1)^4.
        assert 2*d[n]+3*d[n-1]+(n+1)*d[n-2]+(n-5)*d[n-3] == 0
    report(f'PASS: first 17 A189281 corrections match prior results; generated orders 0..{order}.')
    report(f'PASS: {order-5} auxiliary inverse-factorial recurrence equations.')
    S = [[0]*(order+1) for _ in range(order+1)]
    S[0][0]=1
    for a in range(1,order+1):
        for b in range(1,a+1):
            S[a][b]=S[a-1][b-1]+b*S[a-1][b]
    for J in range(1,order+1):
        assert c[J] == sum(d[m]*S[J-1][m-1] for m in range(1,J+1))
    report(f'PASS: {order} inverse-factorial/Stirling-transform comparisons.')
    sharp = 0
    for r,s in pairs:
        BP = correction_polynomials(min(order,40),r,s)
        if r>=2 and s>=2:
            D=r+s
            for J in range(2*D,len(BP)):
                assert len(BP[J])-1 == J-D
                assert BP[J][-1] == a_weight(D,r,s)
                sharp += 1
    report(f'PASS: {sharp} sharp-degree and leading-coefficient checks across offset pairs.')
    samples = {}
    for r,s in [(1,1),(1,3),(2,2),(2,3),(3,3),(4,4),(5,5)]:
        BP = correction_polynomials(12,r,s)
        samples[f'{r},{s}'] = [sum((-1)**h*v for h,v in enumerate(row)) for row in BP]
    result = {'order': order, 'B_polynomials': B, 'avoidance_coefficients': c,
              'inverse_falling_factorial_coefficients': d,
              'sample_offsets': samples, 'polynomial_identity_checks': count,
              'histogram_checks': nchecks, 'stable_moment_checks': mchecks,
              'oeis_value_checks': oeis_checked, 'sharp_degree_checks': sharp,
              'elapsed_seconds': round(time.monotonic()-started,3)}
    outdir.mkdir(parents=True,exist_ok=True)
    (outdir/'coefficients.json').write_text(json.dumps(result,indent=2)+'\n')
    (outdir/'verification.txt').write_text('\n'.join(log)+'\n')
    print('A189281 c[0:25] =',c[:25])
    print('Factorial d[0:20] =',d[:20])
    print('Sample offsets:',samples)
    print('Seconds:',result['elapsed_seconds'])
    return result

if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: verification requires assertions.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=100)
    parser.add_argument('--identity-order',type=int,default=16)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=parser.parse_args()
    if args.order<16 or not 4<=args.identity_order<=30:
        parser.error('Use --order >= 16 and 4 <= --identity-order <= 30.')
    run(args.order,args.identity_order,args.output)
