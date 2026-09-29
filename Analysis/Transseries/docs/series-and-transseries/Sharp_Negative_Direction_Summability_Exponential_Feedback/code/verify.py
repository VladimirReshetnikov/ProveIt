#!/usr/bin/env python3
"""Exact coefficient checks and non-interval high-precision remainder diagnostics.

The proof is in article.tex. This program tests finite identities, not asymptotic
statements. Integer b[n] is n! times the ordinary coefficient of U.
"""
from __future__ import annotations
import argparse
import csv
import json
from fractions import Fraction
from math import comb, factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def coefficients(slopes: list[int], order: int) -> list[int]:
    """Compute n! [q^n]U exactly using exponential Bell recurrences."""
    if order < 1 or len(slopes) <= order or any(x < 0 for x in slopes):
        raise ValueError('Supply nonnegative integer slopes through the order.')
    facts = [factorial(n) for n in range(order + 1)]
    b = [0] * (order + 1)
    e = [[1] + [0] * order for _ in range(order + 1)]
    for n in range(1, order + 1):
        b[n] = sum(facts[n] // facts[n-j] * e[j][n-j]
                   for j in range(1, n + 1))
        for j in range(1, order - n + 1):
            e[j][n] = slopes[j] * sum(
                comb(n-1, m-1) * b[m] * e[j][n-m]
                for m in range(1, n+1))
    return b


def partitions(n: int, largest: int | None = None):
    """Yield multiplicity dictionaries for integer partitions, independently."""
    if n == 0:
        yield {}
        return
    if largest is None:
        largest = n
    for j in range(min(n, largest), 0, -1):
        for rest in partitions(n-j, j):
            ans = rest.copy()
            ans[j] = ans.get(j, 0) + 1
            yield ans


def lagrange_coefficient(slopes: list[int], n: int) -> Fraction:
    ans = Fraction(0)
    for counts in partitions(n):
        k = sum(counts.values())
        slope = sum(slopes[j] * m for j, m in counts.items())
        den = 1
        for m in counts.values():
            den *= factorial(m)
        ans += Fraction(slope ** (k-1), den)  # 0**0=1 is intended.
    return ans


def kernel_coefficient(slopes: list[int], n: int, B=Fraction(1)) -> Fraction:
    return sum((B*slopes[j]) ** (n+1-j) / factorial(n+1-j)
               for j in range(1, n+2))


def exact_checks(order: int) -> dict:
    data = ROOT / 'data'
    data.mkdir(exist_ok=True)
    report = {'order': order, 'partition_checks': 0,
              'kernel_lower_bound_checks': 0, 'analytic_benchmark_checks': 0,
              'passed': True, 'first_coefficients': {}}
    for name, fn in [('zero', lambda j: 0), ('linear', lambda j: j),
                     ('quadratic', lambda j: j*j), ('cubic', lambda j: j*j*j)]:
        slopes = [fn(j) for j in range(order+2)]
        b = coefficients(slopes, order)
        u = [Fraction(b[n], factorial(n)) for n in range(order+1)]
        for n in range(1, min(order, 12)+1):
            assert u[n] == lagrange_coefficient(slopes, n), (name, n)
            report['partition_checks'] += 1
        for n in range(order):
            assert kernel_coefficient(slopes, n) <= u[n+1], (name, n)
            report['kernel_lower_bound_checks'] += 1
        if name == 'zero':
            assert all(x == 1 for x in u[1:])
            report['analytic_benchmark_checks'] += order
        if name == 'linear':
            # U=q(1+U)e^U, independent one-variable Lagrange formula.
            for n in range(1, order+1):
                value = sum(Fraction(comb(n, h)*n**(n-1-h), factorial(n-1-h))
                            for h in range(n))/n
                assert value == u[n]
                report['analytic_benchmark_checks'] += 1
        report['first_coefficients'][name] = [str(x) for x in u[1:9]]
        with (data / f'{name}_coefficients.csv').open('w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['n', 'n_factorial_times_u_n', 'u_n_numerator',
                             'u_n_denominator'])
            for n in range(1, order+1):
                writer.writerow([n, b[n], u[n].numerator, u[n].denominator])
    return report


def numerical_checks() -> dict:
    """mpmath diagnostics; no interval or directed-rounding claim."""
    import mpmath as mp
    mp.mp.dps = 100
    eta = mp.mpf('0.5')
    delta = eta/4
    c = eta-delta
    B = 1+delta
    rows = []
    count = 0
    for p in (2, 3):
        for r, angle in [('0.01', '0'), ('0.005', '0'), ('0.01', '0.35')]:
            r, angle = mp.mpf(r), mp.mpf(angle)
            q = -r*mp.exp(mp.j*angle)
            kappa = r + r/(mp.e*c*(1-r))
            L, steps = 18, 24
            def F(v, length):
                return mp.fsum(q**(j-1)*mp.exp((j**p)*q*v)
                               for j in range(1, length+1))
            v = mp.mpf(1)
            first = F(v, L)
            increment = abs(first-v)
            for _ in range(steps):
                v = F(v, L)
            U = q*v
            ref = mp.mpf(1)
            for _ in range(60):
                ref = F(ref, 60)
            Uref = q*ref
            bound = r*kappa**steps/(1-kappa)*increment + r**(L+1)/((1-kappa)*(1-r))
            assert abs(U-Uref) <= bound
            # Uniform kernel remainder inequality at a genuinely complex v.
            for vv in [mp.mpf(1), mp.mpf(1)+mp.j*mp.mpf('0.06')]:
                for N in [2, 4, 8, 12]:
                    def aa(n, v):
                        return mp.fsum(((j**p)*v)**(n+1-j)/mp.factorial(n+1-j)
                                       for j in range(1, n+2))
                    exact = F(vv, 70)
                    poly = mp.fsum(aa(n, vv)*q**n for n in range(N))
                    rhs = aa(N, B)*r**N/(1-r)
                    assert abs(exact-poly) <= rhs
                    count += 1
            rows.append({'p': p, 'r': str(r), 'angle_from_negative_axis': str(angle),
                         'U_real': mp.nstr(mp.re(U), 90),
                         'U_imag': mp.nstr(mp.im(U), 90),
                         'kappa_bound': mp.nstr(kappa, 12),
                         'analytic_error_bound': mp.nstr(bound, 10),
                         'comparison_difference': mp.nstr(abs(U-Uref), 10),
                         'actions': L, 'iterations': steps})
    with (ROOT/'data'/'sectorial_diagnostics.csv').open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader(); w.writerows(rows)
    return {'precision_decimal_digits': 100, 'interval_arithmetic': False,
            'kernel_remainder_checks': count, 'finite_solver_comparisons': len(rows),
            'rows': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=120)
    parser.add_argument('--exact-only', action='store_true')
    args = parser.parse_args()
    if not 12 <= args.order <= 500:
        parser.error('--order must be between 12 and 500')
    report = {'exact': exact_checks(args.order)}
    if not args.exact_only:
        report['numerical'] = numerical_checks()
    (ROOT/'data'/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
