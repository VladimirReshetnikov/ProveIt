#!/usr/bin/env python3
"""Exact checks for A293239; Python standard library only.

This verifies a finite range, not the all-n conjecture.  It also compares
independent derivative, shifted-product, and triangle computations.
Usage: python3 verify.py --max-n 1500 --data-dir data
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from fractions import Fraction
from collections import defaultdict
from pathlib import Path

OEIS_HEAD = [1,2,4,7,11,15,21,28,35,43,53,64,76,88,102,117,133,149,
             167,186,206,226,248,271,295,319,345,372,400,428,458,489,
             521,553,587,622,658,694,732,771,811,851,893,936,980,1024,
             1070,1117,1165,1213,1263,1314,1366,1418]

def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)

def candidate(n: int) -> int:
    if n < 0:
        raise ValueError('n must be nonnegative')
    return 1 if n == 0 else 1+n*(n+1)//2-(n-1)//4-int(n >= 8)

def known_zero(m: int, r: int) -> bool:
    return (m, r) == (8, 5) or (m >= 5 and m % 4 == 1 and r == (m-1)//2)

def product_coefficient(m: int, r: int) -> int:
    """[u^r] product_{j=0}^{m-1}(u+r-j), truncated exactly."""
    coefficients = [1] + [0]*r
    for j in range(m):
        v = r-j
        coefficients = [v*coefficients[0]] + [
            v*coefficients[k]+coefficients[k-1] for k in range(1, r+1)]
    return coefficients[r]

def is_prime(p: int) -> bool:
    return p >= 2 and all(p % d for d in range(2, math.isqrt(p)+1))

def valuation(v: int, p: int) -> int:
    require(v != 0, 'valuation of zero is undefined')
    v = abs(v)
    count = 0
    while v % p == 0:
        count += 1
        v //= p
    return count

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=1500)
    parser.add_argument('--data-dir', type=Path, default=Path('data'))
    args = parser.parse_args()
    N = args.max_n
    if not 60 <= N <= 100000:
        parser.error('--max-n must be between 60 and 100000')
    args.data_dir.mkdir(parents=True, exist_ok=True)
    pp, previous = [1], [0, 1]
    small = [[1], [0, 1]]
    counts = [1, 2]
    zeros: list[tuple[int, int]] = []
    valuation_checks = 0
    primes = [p for p in range(2, 102) if is_prime(p)]
    for m in range(2, N+1):
        p, q = previous+[0], pp+[0, 0]
        current = [0]+[(r-m+1)*p[r]+p[r-1]+(m-1)*q[r-1]
                      for r in range(1, m+1)]
        row_zeros = [r for r in range(1, m+1) if current[r] == 0]
        zeros.extend((m, r) for r in row_zeros)
        require(all(known_zero(m, r) for r in row_zeros), f'unexpected zero in row {m}')
        expected = [r for r in range(1, m+1) if known_zero(m, r)]
        require(row_zeros == expected, f'missing known zero in row {m}')
        counts.append(counts[-1]+m-len(row_zeros))
        require(counts[-1] == candidate(m), f'count mismatch at n={m}')
        require(m+1+m*m//4 <= counts[-1], f'quadratic lower bound failed at {m}')
        if m <= 60:
            small.append(current[:])
        if m <= 500:
            for prime in primes:
                if prime <= m:
                    r = m-prime+1
                    require(valuation(current[r], prime) == valuation(m//prime, prime),
                            f'prime-offset valuation failed at {(m, r, prime)}')
                    valuation_checks += 1
        pp, previous = previous, current
    require(counts[:len(OEIS_HEAD)] == OEIS_HEAD, 'OEIS displayed head mismatch')
    product_checks = 0
    for m in range(31):
        for r in range(m+1):
            require(product_coefficient(m, r) == small[m][r], f'product check {(m, r)}')
            product_checks += 1
    # Exact checks of the column formulas, including the monotonicity brackets.
    harmonic = [Fraction(0)]
    harmonic2 = [Fraction(0)]
    for t in range(1, 61):
        harmonic.append(harmonic[-1]+Fraction(1,t))
        harmonic2.append(harmonic2[-1]+Fraction(1,t*t))
    g = [6-11*harmonic[t]+3*(harmonic[t]**2-harmonic2[t]) for t in range(61)]
    require(g[19] == Fraction(-4571462267,97772875200), 'g(19) bracket')
    require(g[20] == Fraction(537826687,1150269120), 'g(20) bracket')
    for t in range(60):
        require(g[t+1]-g[t] == (6*harmonic[t]-11)/(t+1), 'column-3 difference identity')
    column_checks = 0
    for m in range(1,61):
        expected = 1 if m == 1 else (-1)**m*math.factorial(m-2)
        require(small[m][1] == expected, f'column 1 at {m}')
        column_checks += 1
        if m >= 2:
            expected = 1 if m == 2 else (-1)**m*math.factorial(m-3)*(2*harmonic[m-3]-3)
            require(small[m][2] == expected, f'column 2 at {m}')
            column_checks += 1
        if m >= 3:
            expected = 1 if m == 3 else (-1)**(m-4)*math.factorial(m-4)*g[m-4]
            require(small[m][3] == expected, f'column 3 at {m}')
            column_checks += 1
    # Independent formal derivative recurrence for every coefficient, not just counts.
    polynomial: dict[tuple[int, int], int] = {(0, 0): 1}
    derivative_checks = 0
    for n in range(61):
        reconstructed: dict[tuple[int, int], int] = {}
        for m in range(n+1):
            for r in range(m+1):
                value = math.comb(n, m)*small[m][r]
                if value:
                    reconstructed[m-r, n-m] = value
        require(polynomial == reconstructed, f'derivative polynomial mismatch at n={n}')
        require(len(polynomial) == counts[n], f'derivative count mismatch at n={n}')
        derivative_checks += 1
        next_poly: defaultdict[tuple[int, int], int] = defaultdict(int)
        for (k, j), v in polynomial.items():
            next_poly[k, j] += v
            next_poly[k, j+1] += v
            next_poly[k+1, j] -= k*v
            if j:
                next_poly[k+1, j-1] += j*v
        polynomial = {key: val for key, val in next_poly.items() if val}
    # The numerator of the proposed rational generating function, checked exactly.
    numerator = {0:1, 2:1, 3:1, 6:1, 8:-1, 9:1, 12:1, 13:-1}
    denominator = {0:1, 1:-2, 2:1, 4:-1, 5:2, 6:-1}
    for n in range(N+1):
        residual = sum(c*candidate(n-j) for j, c in denominator.items() if j <= n)
        require(residual == numerator.get(n, 0), f'generating-function check at {n}')
    gmp_compared = 0
    if (args.data_dir/'counts.csv').exists():
        with (args.data_dir/'counts.csv').open(newline='') as f:
            for row in csv.DictReader(f):
                n = int(row['n'])
                if n <= N:
                    require(int(row['actual_count']) == counts[n], f'GMP cross-check at {n}')
                    gmp_compared += 1
    report = {
        'max_n': N, 'triangle_entries_tested': N*(N+1)//2,
        'zero_entries': len(zeros), 'unexpected_zero_entries': 0,
        'actual_final_count': counts[-1], 'candidate_final_count': candidate(N),
        'displayed_oeis_terms_checked': len(OEIS_HEAD),
        'shifted_product_entries_checked_through_row_30': product_checks,
        'complete_derivative_polynomials_checked_through_n_60': derivative_checks,
        'prime_offset_valuation_checks': valuation_checks,
        'first_three_column_formula_checks': column_checks,
        'gmp_count_rows_compared': gmp_compared,
        'status': 'All checks passed. Finite verification is not an all-n proof.'}
    (args.data_dir/'python_report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
