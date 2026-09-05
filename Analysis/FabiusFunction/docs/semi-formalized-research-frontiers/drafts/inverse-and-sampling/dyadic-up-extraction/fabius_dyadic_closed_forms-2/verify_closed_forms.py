#!/usr/bin/env python3
"""Exact checks for recurrence-free dyadic Fabius / Rvachev formulas.

Python 3.10+; standard library only. No floating-point arithmetic is used.
Every evaluator is a finite expression. Enumerating compositions/partitions is
not a recurrence for Fabius values or moments. The optional moment oracle is
explicitly labelled: it is only an independent verification mechanism.

Run: python verify_closed_forms.py --max-depth 8
"""
from __future__ import annotations
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial, comb, prod
import argparse
import json
from pathlib import Path


def pow2(k: int) -> Q:
    return Q(2**k) if k >= 0 else Q(1, 2**(-k))


def triangular(n: int) -> int:
    return n*(n+1)//2


def tm(k: int) -> int:
    if k < 0:
        raise ValueError('Thue--Morse index must be nonnegative')
    return 1 if k.bit_count() % 2 == 0 else -1


def compositions(k: int):
    """All positive ordered compositions, using cut subsets, not a recurrence."""
    if k == 0:
        yield ()
        return
    for mask in range(1 << (k-1)):
        cuts = [0] + [j for j in range(1, k) if mask & (1 << (j-1))] + [k]
        yield tuple(b-a for a, b in zip(cuts, cuts[1:]))


@lru_cache(None)
def profiles(k: int) -> tuple[tuple[int, ...], ...]:
    """Multiplicity vectors (v_1,...,v_k), sum j*v_j=k, finite enumeration."""
    if k == 0:
        return ((),)
    return tuple(v for v in product(*(range(k//j+1) for j in range(1, k+1)))
                 if sum(j*vj for j, vj in enumerate(v, 1)) == k)


@lru_cache(None)
def bernoulli(n: int) -> Q:
    """Finite double sum, with B_1=-1/2."""
    return sum((Q(sum((-1)**v*comb(j, v)*v**n for v in range(j+1)), j+1)
                for j in range(n+1)), Q(0))


@lru_cache(None)
def lam(r: int) -> Q:
    if r < 1:
        raise ValueError('r must be positive')
    return Q(2**(2*r-1), r*factorial(2*r)*(4**r-1))*bernoulli(2*r)


@lru_cache(None)
def moment_coefficient(k: int) -> Q:
    """[t^(2k)] M(t), using positive compositions (no moment recurrence)."""
    total = Q(0)
    for c in compositions(k):
        suffix = k
        term = Q(1)
        for a in c:
            term /= factorial(2*a+1)*(4**suffix-1)
            suffix -= a
        total += term
    return total


@lru_cache(None)
def bell_coefficient(k: int, inverse: bool = False) -> Q:
    """[t^(2k)] M(t) or 1/M(t), via explicit Bernoulli-partition sums."""
    sign = -1 if inverse else 1
    return sum((prod(((sign*lam(r))**v / factorial(v)
                      for r, v in enumerate(profile, 1)), start=Q(1))
                for profile in profiles(k)), Q(0))


def phi(degree: int, x: Q | int) -> Q:
    """[t^degree] exp(x*t) M(t), using the composition formula."""
    if degree < 0:
        return Q(0)
    x = Q(x)
    return sum((moment_coefficient(k)*x**(degree-2*k)/factorial(degree-2*k)
                for k in range(degree//2+1)), Q(0))


def check_input(a: int, n: int):
    if n < 0 or not 0 <= a <= 2**n:
        raise ValueError('Require n>=0 and 0<=a<=2^n')


def fabius_moment(a: int, n: int) -> Q:
    check_input(a, n)
    return pow2(-triangular(n))*sum((tm(h)*phi(n, 2*a-2*h-1)
                                    for h in range(a)), Q(0))


def fabius_binary(a: int, n: int) -> Q:
    """At most popcount(a) blocks; all coefficients are explicit finite sums."""
    check_input(a, n)
    total = Q(0)
    for j in range(a.bit_length()):
        if a & (1 << j):
            higher = a >> (j+1)
            remainder = a % (1 << j)
            A = 1 + Q(2*remainder, 1 << j)
            d = n-j
            total += tm(higher)*pow2(-triangular(d))*phi(d, A)
    return total


def centered_spline_at_grid(a: int, n: int, N: int) -> Q:
    """CDF G_N(a/2^n), N>=n and N>=1, a single integer power sum."""
    check_input(a, n)
    if N < max(n, 1):
        raise ValueError('Need N>=max(n,1)')
    A = a << (N-n)
    B = sum(tm(h)*(2*A-2*h-1)**N for h in range(A))
    return Q(B, factorial(N)*2**triangular(N))


def centered_spline(x: Q, N: int) -> Q:
    """CDF G_N at any rational input, including exact knot endpoints."""
    if N < 1:
        raise ValueError('Need N>=1')
    x = Q(x)
    A = 2**(N+1)*x - 1
    den = A.denominator
    numer = A.numerator
    B = sum(tm(h)*max(numer-2*h*den, 0)**N for h in range(2**N))
    return Q(B, den**N*factorial(N)*2**triangular(N))


def qpoch(q: Q, length: int) -> Q:
    return prod((1-q**j for j in range(1, length+1)), start=Q(1))


def lagrange_weight(d: int, j: int, q: Q = Q(1, 4)) -> Q:
    if not 0 <= j <= d:
        raise ValueError('Need 0<=j<=d')
    return (-1)**(d-j)*q**triangular(d-j)/(qpoch(q, j)*qpoch(q, d-j))


def fabius_quarter(a: int, n: int, offset: int = 0) -> Q:
    """Exact quarter-base extraction: d+1 prefixes, d=floor(n/2)."""
    check_input(a, n)
    if n == 0:
        return Q(a)
    if offset < 0:
        raise ValueError('offset must be nonnegative')
    d = n//2
    return sum((lagrange_weight(d, j)*centered_spline_at_grid(a, n, n+offset+j)
                for j in range(d+1)), Q(0))


def fabius_derivative(a: int, n: int, r: int) -> Q:
    """Exact derivative at a dyadic point, by differentiated head--tail formula."""
    check_input(a, n)
    if r < 0:
        raise ValueError('r must be nonnegative')
    if r > n:
        return Q(0)
    return pow2((n+1)*r-triangular(n))*sum(
        (tm(h)*phi(n-r, 2*a-2*h-1) for h in range(a)), Q(0))


def spline_jet_prediction(a: int, n: int, N: int, h: Q) -> Q:
    """Exact local identity, valid for |h|<=2^(-N-1), N>=n>=1."""
    if N < n or n < 1 or abs(h) > pow2(-N-1):
        raise ValueError('Outside the exact local cell')
    return sum((bell_coefficient(k, inverse=True)*pow2(-2*k*(N+1))
                *h**j/factorial(j)*fabius_derivative(a, n, j+2*k)
                for k in range(n//2+1) for j in range(n-2*k+1)), Q(0))


def prefix_moment_coefficient(k: int, N: int) -> Q:
    """[t^(2k)] M_N(t), using a finite Thue--Morse power sum."""
    if N == 0:
        return Q(int(k == 0))
    exponent = 2*k+N
    B = sum(tm(h)*(2**N-1-2*h)**exponent for h in range(2**N))
    return pow2(N*(N-1)//2-N*exponent)*Q(B, factorial(exponent))


def recovered_moment_coefficient(k: int) -> Q:
    return sum((lagrange_weight(k, j)*prefix_moment_coefficient(k, j)
                for j in range(k+1)), Q(0))


def denominator_bound(n: int) -> int:
    d = n//2
    return 2**triangular(n)*factorial(n+d)*prod(4**j-1 for j in range(1, d+1))



def fabius_rounded(a: int, n: int) -> Q:
    """Certified exact rounding. Exponential cost makes this a small-depth demo."""
    check_input(a, n)
    if n == 0:
        return Q(a)
    D = denominator_bound(n)
    N = max(n, D.bit_length()+1)  # 2**N > 2*D, strictly
    y = D*centered_spline_at_grid(a, n, N) + Q(1, 2)
    return Q(y.numerator//y.denominator, D)


def base_spline(b: int, x: Q, N: int) -> Q:
    """Centered prefix CDF for X_b=(b-1)*sum_{j>=1} b^-j U_j."""
    if b < 2 or N < 1:
        raise ValueError('Need integer b>=2, N>=1')
    total = Q(0)
    for mask in range(2**N):
        shift = sum((Q(b-1, b**j) for j in range(1,N+1)
                     if mask & (1 << (j-1))), Q(0))
        t = max(Q(x)-Q(1,2*b**N)-shift, Q(0))
        total += tm(mask)*t**N
    return total*Q(b**triangular(N), (b-1)**N*factorial(N))


def base_extract(b: int, a: int, n: int, offset: int = 0) -> Q:
    if not 0 <= a <= b**n or n < 1:
        raise ValueError('Need n>=1 and 0<=a<=b^n')
    d = n//2
    return sum((lagrange_weight(d,j,Q(1,b*b))*base_spline(b,Q(a,b**n),n+offset+j)
                for j in range(d+1)), Q(0))


def up_spline(x: Q, N: int) -> Q:
    """Density of sum_{j=1}^N 2^-j V_j, N>=2."""
    if N < 2:
        raise ValueError('Use N>=2 for a continuous spline density')
    x = Q(x)
    A = 2**N*(x+1)-1
    den = A.denominator
    numer = A.numerator
    B = sum(tm(h)*max(numer-2*h*den, 0)**(N-1) for h in range(2**N))
    return Q(B, den**(N-1)*factorial(N-1)*2**(N*(N-1)//2))


def oracle_coefficients(kmax: int) -> list[Q]:
    """Independent verification ONLY; not used by any closed-form evaluator."""
    out = [Q(1)]
    for k in range(1, kmax+1):
        out.append(sum((out[j]/factorial(2*(k-j)+1) for j in range(k)), Q(0))
                   /(4**k-1))
    return out


def verify(max_depth: int = 8) -> dict:
    if not 1 <= max_depth <= 12:
        raise ValueError('Choose 1<=max-depth<=12; exhaustive sums grow exponentially')
    counters = {'grid_points': 0, 'shifted_extractions': 0,
                'local_cell_checks': 0, 'rvachev_spline_checks': 0,
                'moment_checks': 0, 'denominator_checks': 0,
                'rounding_checks': 0, 'generalized_base_checks': 0}
    oracle = oracle_coefficients(8)
    for k in range(9):
        assert moment_coefficient(k) == bell_coefficient(k) == oracle[k]
        assert recovered_moment_coefficient(k) == oracle[k]
        assert ((-1)**k)*bell_coefficient(k, inverse=True) > 0
        counters['moment_checks'] += 1
    for n in range(max_depth+1):
        D = denominator_bound(n)
        for a in range(2**n+1):
            value = fabius_moment(a, n)
            assert value == fabius_binary(a, n) == fabius_quarter(a, n)
            assert value + fabius_binary(2**n-a, n) == 1
            assert (D*value).denominator == 1
            counters['denominator_checks'] += 1
            counters['grid_points'] += 1
        if n >= 1:
            for a in sorted({0, 1, (2**n)//3, (2**n)//2, 2**n-1, 2**n}):
                for offset in (1, 2):
                    assert fabius_quarter(a, n, offset) == fabius_binary(a, n)
                    counters['shifted_extractions'] += 1
    for n in range(1, min(5, max_depth)+1):
        for a in range(2**n+1):
            for N in (n, n+1, n+2):
                for scaled_h in (Q(-1), Q(-1, 2), Q(0), Q(1, 2), Q(1)):
                    h = scaled_h*pow2(-N-1)
                    assert centered_spline(Q(a, 2**n)+h, N) == spline_jet_prediction(a, n, N, h)
                    counters['local_cell_checks'] += 1
            N = n+1
            for sign in (-1, 1):
                x = sign*Q(a, 2**n)
                assert up_spline(x, N) == centered_spline_at_grid(2**n-a, n, N-1)
                d = n//2
                recovered = sum((lagrange_weight(d,j)*up_spline(x, N+j)
                                 for j in range(d+1)), Q(0))
                assert recovered == fabius_binary(2**n-a, n)
                counters['rvachev_spline_checks'] += 1
    # Exact-degree checks: highest even derivative at every reduced point.
    for n in range(1, max_depth+1):
        for a in range(1, 2**n, 2):
            assert fabius_derivative(a, n, 2*(n//2)) != 0
    # Residual-free interpolation of the whole polynomial space.
    for d in range(9):
        for r in range(d+1):
            assert sum((lagrange_weight(d,j)*Q(1,4)**(j*r)
                        for j in range(d+1)), Q(0)) == int(r == 0)
    for n in range(1, 4):
        for a in range(2**n+1):
            assert fabius_rounded(a,n) == fabius_binary(a,n)
            counters['rounding_checks'] += 1
    for b in (2,3,4):
        for n in (1,2,3):
            for a in range(b**n+1):
                v = base_extract(b,a,n)
                assert v == base_extract(b,a,n,1)
                assert v+base_extract(b,b**n-a,n) == 1
                if b == 2:
                    assert v == fabius_binary(a,n)
                counters['generalized_base_checks'] += 1
    assert base_extract(3,1,2) == Q(7,576)
    examples = {f'{a}/{2**n}': str(fabius_binary(a,n))
                for a,n in [(1,1),(1,2),(1,3),(3,3),(1,4),(3,4),
                            (5,4),(7,4),(1,5),(13,5),(21,6),(37,7)]}
    return {'status': 'PASS', 'arithmetic': 'fractions.Fraction and Python integers',
            'max_exhaustive_depth': max_depth, **counters, 'examples': examples,
            'cumulant_log_coefficients': [str(lam(r)) for r in range(1,6)],
            'inverse_mgf_coefficients': [str(bell_coefficient(k, True)) for k in range(6)]}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-depth', type=int, default=8)
    parser.add_argument('--output', type=Path, default=Path('verification_results.json'))
    args = parser.parse_args()
    result = verify(args.max_depth)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
