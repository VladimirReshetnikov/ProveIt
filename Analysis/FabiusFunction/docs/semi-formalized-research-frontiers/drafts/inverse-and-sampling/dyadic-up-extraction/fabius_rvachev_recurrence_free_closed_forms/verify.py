#!/usr/bin/env python3
"""Exact, non-recursive formulae for Fabius/Rvachev dyadic values.

Standard library only; Python 3.9+.  Run `python verify.py` for the
cross-checks reported in the article.  All arithmetic is Fraction/integer.
The composition and partition iterators enumerate finite index sets; no
moment or function-value recurrence is used by any evaluator.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, factorial, prod
import argparse
import json
from pathlib import Path


def eps(k: int) -> int:
    """Thue--Morse sign, directly from the binary expansion."""
    return -1 if bin(k).count('1') % 2 else 1


def compositions(n: int):
    """All ordered positive compositions via cuts in n unit objects."""
    if n < 0:
        raise ValueError('n must be nonnegative')
    if n == 0:
        yield ()
        return
    for mask in range(1 << (n - 1)):
        cuts = [0] + [j for j in range(1, n) if mask & (1 << (j - 1))] + [n]
        yield tuple(cuts[j+1] - cuts[j] for j in range(len(cuts)-1))


def partitions(n: int):
    """Multiplicity vectors k_j with sum(j*k_j)=n, a finite product set."""
    for ks in product(*(range(n // j + 1) for j in range(1, n + 1))):
        if sum((j+1)*k for j,k in enumerate(ks)) == n:
            yield ks


@lru_cache(None)
def bernoulli(n: int) -> Q:
    return sum((Q(sum((-1)**j * comb(k,j) * j**n for j in range(k+1)), k+1)
                for k in range(n+1)), Q(0))


@lru_cache(None)
def central_coefficient(n: int) -> Q:
    """E[Y^(2n)]/(2n)! from a positive composition sum."""
    total = Q(0)
    for a in compositions(n):
        term = Q(1)
        suffix = n
        for r in a:
            term /= factorial(2*r+1) * (4**suffix-1)
            suffix -= r
        total += term
    return total


@lru_cache(None)
def central_partition(n: int, inverse: bool = False) -> Q:
    """[t^(2n)] M_Y(t), or [t^(2n)] 1/M_Y(t), from cumulants."""
    lam = [Q(4**r)*bernoulli(2*r)/
           (2*r*factorial(2*r)*(4**r-1)) for r in range(1,n+1)]
    if inverse:
        lam = [-v for v in lam]
    return sum((prod((lam[j]**k / factorial(k) for j,k in enumerate(ks)), start=Q(1))
                for ks in partitions(n)), Q(0))


@lru_cache(None)
def raw_coefficient(n: int, base: int = 2) -> Q:
    """E[X_base^n]/n!, X_base=(base-1)*sum U_j/base^j."""
    if base < 2:
        raise ValueError('base must be an integer >= 2')
    total = Q(0)
    for a in compositions(n):
        term, suffix = Q((base-1)**n), n
        for r in a:
            term /= factorial(r+1) * (base**suffix-1)
            suffix -= r
        total += term
    return total


def valid_grid(a: int, n: int):
    if n < 0 or not (0 <= a <= 2**n):
        raise ValueError('require n >= 0 and 0 <= a <= 2^n')


def power_sum(a: int, p: int) -> int:
    return sum(eps(h)*(2*a-2*h-1)**p for h in range(a))


def fabius_moments(a: int, n: int, partition: bool = False) -> Q:
    valid_grid(a,n)
    coeff = central_partition if partition else central_coefficient
    return sum((coeff(j)*Q(power_sum(a,n-2*j), factorial(n-2*j))
                for j in range(n//2+1)), Q(0)) / 2**(n*(n+1)//2)


@lru_cache(None)
def weight(d: int, j: int, q: Q = Q(1,4)) -> Q:
    if not (0 <= j <= d) or not (0 < q < 1):
        raise ValueError('require 0 <= j <= d and 0 < q < 1')
    return prod((Q(-q**ell, q**j-q**ell) for ell in range(d+1) if ell != j), start=Q(1))


def centered_cdf(a: int, n: int, N: int) -> Q:
    """CDF of X_N + 2^(-N-1) at a/2^n, for N >= n >= 1."""
    if not (N >= n >= 1):
        raise ValueError('require N >= n >= 1')
    M = a * 2**(N-n)
    return Q(sum(eps(k)*(2*M-2*k-1)**N for k in range(M)),
             factorial(N)*2**(N*(N+1)//2))


def fabius_quarter(a: int, n: int, start_offset: int = 0) -> Q:
    valid_grid(a,n)
    if n == 0:
        return Q(a)
    d = n//2
    return sum((weight(d,j)*centered_cdf(a,n,n+start_offset+j)
                for j in range(d+1)), Q(0))


def shifted_power_cdf(a: int, n: int, N: int, alpha: Q) -> Q:
    """Polynomial continuation of the shifted spline value; alpha arbitrary."""
    M = a*2**(N-n)
    return sum((eps(k)*(Q(M-k)-alpha)**N for k in range(M)),Q(0)) / (
        factorial(N)*2**(N*(N-1)//2))


def fabius_half(a: int, n: int, alpha: Q = Q(1,2)) -> Q:
    if n == 0:
        return Q(a)
    return sum((weight(n,j,Q(1,2))*shifted_power_cdf(a,n,n+j,alpha)
                for j in range(n+1)),Q(0))


def fabius_bits(a: int, n: int) -> Q:
    valid_grid(a,n)
    if a == 0 or a == 2**n:
        return Q(a,2**n)
    bits = [b for b in range(1,n+1) if a & (1 << (n-b))]
    result = Q(0)
    for i,b in enumerate(bits):
        residual = sum((Q(1,2**v) for v in bits[i+1:]),Q(0))
        s = residual*2**b
        poly = sum((raw_coefficient(b-k)*s**k/factorial(k) for k in range(b+1)),Q(0))
        result += (-1)**i * poly/2**(b*(b-1)//2)
    return result


def determinant(mat):
    """Fraction-free Bareiss determinant (matrix is copied)."""
    A = [list(row) for row in mat]
    n = len(A)
    if n == 0:
        return 1
    prev, sign = 1, 1
    for k in range(n-1):
        if A[k][k] == 0:
            pivot = next((i for i in range(k+1,n) if A[i][k]),None)
            if pivot is None:
                return 0
            A[k],A[pivot] = A[pivot],A[k]
            sign = -sign
        p = A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                z = A[i][j]*p-A[i][k]*A[k][j]
                assert z % prev == 0
                A[i][j] = z//prev
            A[i][k] = 0
        prev = p
    return sign*A[-1][-1]


def fabius_determinant(a: int, n: int) -> Q:
    valid_grid(a,n)
    d = n//2
    t = [comb(n,2*j)*power_sum(a,n-2*j) for j in range(d+1)]
    A = []
    for k in range(1,d+1):
        A.append([(2*k+1)*(4**k-1) if j==k else
                  -comb(2*k+1,2*j) if j<k else 0
                  for j in range(1,d+1)] + [1])
    A.append([-t[j] for j in range(1,d+1)]+[t[0]])
    den = 2**(n*(n+1)//2)*factorial(n)*prod((2*k+1)*(4**k-1) for k in range(1,d+1))
    return Q(determinant(A),den)


def at_fraction(x: Q) -> Q:
    x = Q(x)
    if x <= 0:
        return Q(0)
    if x >= 1:
        return Q(1)
    den = x.denominator
    if den & (den-1):
        raise ValueError('argument is not dyadic')
    return fabius_moments(x.numerator,den.bit_length()-1)


def global_at(x: Q) -> Q:
    if x < 0:
        return Q(0)
    m = int(x//2)
    t = x-2*m
    return eps(m)*at_fraction(min(t,2-t))


def up_at(x: Q) -> Q:
    return Q(0) if abs(x) >= 1 else at_fraction(1-abs(x))


def fabius_derivative(x: Q, r: int) -> Q:
    if r == 0:
        return at_fraction(x)
    if not (0 < x < 1):
        return Q(0)
    return 2**(r*(r+1)//2)*global_at(2**r*x)


def up_spline(a: int, n: int, N: int) -> Q:
    """N centered uniforms; sinc factors indexed 0,...,N-1."""
    if not (N > n >= 0):
        raise ValueError('require N > n >= 0')
    if abs(a) >= 2**n:
        return Q(0)
    A = 2**N+a*2**(N-n)
    return Q(sum(eps(k)*(A-1-2*k)**(N-1) for k in range(A//2)),
             factorial(N-1)*2**(N*(N-1)//2))


def up_quarter(a: int, n: int) -> Q:
    return sum((weight(n//2,j)*up_spline(a,n,n+1+j) for j in range(n//2+1)),Q(0))


def base_moments(a: int, n: int, b: int) -> Q:
    if n == 0:
        return Q(a)
    total = Q(0)
    for bits in product((0,1),repeat=n):
        m = a-(b-1)*sum(v*b**j for j,v in enumerate(bits))
        if m >= 1:
            total += (-1)**sum(bits)*sum((raw_coefficient(l,b)*Q((m-1)**(n-l),factorial(n-l))
                                         for l in range(n+1)),Q(0))
    return total/((b-1)**n*b**(n*(n-1)//2))


def base_spline(a: int, n: int, N: int, b: int) -> Q:
    M = a*b**(N-n)
    num = 0
    for bits in product((0,1),repeat=N):
        v = 2*M-1-2*(b-1)*sum(bit*b**j for j,bit in enumerate(bits))
        if v > 0:
            num += (-1)**sum(bits)*v**N
    return Q(num,2**N*(b-1)**N*b**(N*(N-1)//2)*factorial(N))


def base_quarter(a: int, n: int, b: int) -> Q:
    if n == 0:
        return Q(a)
    return sum((weight(n//2,j,Q(1,b*b))*base_spline(a,n,n+j,b)
                for j in range(n//2+1)),Q(0))


def run_tests(max_depth: int = 8):
    counts = {}
    for j in range(9):
        assert central_coefficient(j) == central_partition(j)
    counts['central_moment_coefficients'] = 9
    known = [Q(1),Q(1,2),Q(5,72),Q(1,288),Q(143,2073600),
             Q(19,33177600),Q(1153,561842749440),Q(583,179789679820800)]
    for n,v in enumerate(known):
        assert fabius_moments(1,n) == v
    count = 0
    for n in range(max_depth+1):
        for a in range(2**n+1):
            v = fabius_moments(a,n)
            assert fabius_moments(a,n,True) == v
            assert fabius_bits(a,n) == v
            assert fabius_determinant(a,n) == v
            assert fabius_quarter(a,n) == v
            assert v+fabius_moments(2**n-a,n) == 1
            assert fabius_moments(2*a,n+1) == v
            count += 1
    counts['complete_grid_cases_five_formulas'] = count
    count = 0
    for n in range(1,7):
        for a in range(1,2**n):
            x = Q(a,2**n)
            for N in (n,n+1,n+3):
                predicted = sum((central_partition(j,True)*Q(1,2**(2*j*(N+1))) *
                                 fabius_derivative(x,2*j) for j in range(n//2+1)),Q(0))
                assert centered_cdf(a,n,N) == predicted
                count += 1
    counts['exact_centered_spline_polynomials'] = count
    count = 0
    for n in range(6):
        for a in range(-2**n,2**n+1):
            assert up_quarter(a,n) == up_at(Q(a,2**n))
            count += 1
    counts['rvachev_direct_spline_cases'] = count
    count = 0
    for n in range(1,6):
        for a in sorted(set((1,2**n//2,2**n-1))):
            for alpha in (Q(0),Q(1,2),Q(1),Q(-2),Q(2,3)):
                assert fabius_half(a,n,alpha) == fabius_moments(a,n)
                count += 1
    counts['half_base_arbitrary_shift_cases'] = count
    count = 0
    for b in (3,4,5):
        for n in range(1,5):
            for a in range(b**n+1):
                assert base_quarter(a,n,b) == base_moments(a,n,b)
                count += 1
    counts['other_integer_base_cases'] = count
    counts['sample_values'] = {f'F({a}/16)':str(fabius_moments(a,4)) for a in range(1,9)}
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-depth',type=int,default=8)
    parser.add_argument('--json',type=Path,help='optionally save test report')
    args = parser.parse_args()
    report = run_tests(args.max_depth)
    text = json.dumps(report,indent=2)
    print(text)
    if args.json:
        args.json.write_text(text+'\n',encoding='utf-8')
