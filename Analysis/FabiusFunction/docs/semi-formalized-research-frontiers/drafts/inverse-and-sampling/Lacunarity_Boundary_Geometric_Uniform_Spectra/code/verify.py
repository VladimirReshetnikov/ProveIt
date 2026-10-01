#!/usr/bin/env python3
"""Exact regression checks for The Lacunarity Boundary.

Uses only the Python standard library. Finite assertions do not prove the
infinite-dimensional or analytic theorems. Decimal outputs are diagnostics,
not interval enclosures. The default output directory is results-rerun/, so
recorded results are not overwritten by a plain invocation.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import random
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction as F
from pathlib import Path

COUNTS: Counter[str] = Counter()


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    COUNTS[name] += 1


def sqroot_distance_bound(x: F, y: F, bound: F) -> bool:
    """Decide (sqrt(x)-sqrt(y))**2 <= bound using rational arithmetic."""
    assert x >= 0 and y >= 0 and bound >= 0
    z = x + y - bound
    return z <= 0 or z * z <= 4 * x * y


def geometric_tests(rng: random.Random) -> None:
    for q in [F(1, 9), F(1, 4), F(4, 9), F(9, 16)]:
        c = (1 - q) / (1 + q)
        for _ in range(70):
            n = rng.randint(2, 15)
            raw = [F(rng.randint(1, 5))]
            for _ in range(n - 1):
                raw.append(raw[-1] * q * F(rng.randint(1, 10), 10))
            total = sum(raw)
            p = [x / total for x in raw]
            b = [(1 - q) * q**j for j in range(n)]
            delta = sum(x*x for x in p) - c
            d = p[0] - (1 - q)
            check('head_nonnegative', d >= 0)
            check('fourth_power_minimum', delta >= 0)
            check('sharp_head_quadratic',
                  delta >= 2*c*d + 2*d*d/(1+q))
            Ds = [sum(p[:k]) - (1-q**k) for k in range(1, n+1)]
            for v in Ds:
                check('cumulative_majorization', v >= 0)
            # For k >= n the padded sequence has zero tail and D_k=q**k.
            weighted_D = sum(q**(k-1)*Ds[k-1] for k in range(1, n))
            weighted_D += q**(2*n-1)/(1-q*q)
            squared_error = sum(x*x for x in p) - 2*sum(x*y for x,y in zip(p,b)) + c
            check('infinite_energy_identity',
                  delta == squared_error + 2*(1-q)**2*weighted_D)
            for j in range(n+5):
                x = p[j] if j < n else F(0)
                y = (1-q)*q**j
                slack = p[0]*q**j - x
                check('envelope_slack', 0 <= slack <= d)
                check('coordinate_square_error', abs(x-y) <= d)
                check('radical_error_bound', sqroot_distance_bound(x,y,d))
                check('prefix_error_bound', sqroot_distance_bound(x,y,d*d/y))
        for d in [F(0), q/7, q/3, q/2, q]:
            x = 1-q+d
            exact = x*x + c*(1-x)**2 - c
            check('sharp_head_equality_family',
                  exact == 2*c*d + 2*d*d/(1+q))


def witness_tests() -> None:
    for n in range(3, 65):
        h = F(1, 2**n)
        c2 = 1/(1-3*h*h)
        check('deleted_variance', c2*(F(1,3)-h*h) == F(1,3))
        T = c2*c2*(F(1,15)-h**4)
        gap = F(2,15)*(T-F(1,15))
        formula = F(4,75)*h*h*(1-4*h*h)/(1-3*h*h)**2
        check('deleted_fourth_moment_identity', gap == formula)
        check('deleted_support', c2*(1-h)**2 <= 1)
        check('deleted_gap_at_least_h_over_three', c2 <= F(16,9))
        check('deleted_TV_bound_constant',
              F(2,3) + F(9,4)/(1-3*h*h) <= 4)
        for r in range(101):
            shifted = max(0, r-n+2)
            # Exact squared derivative-norm ratio versus the K-class bound.
            ratio_sq = F(2**(2*shifted), 1)/c2**(r+1)
            check('smooth_class_all_tested_orders', ratio_sq <= 2**(2*(r+1)))
        for theta in [F(1,2), F(3,4), F(9,10), F(99,100)]:
            lam = 1-theta*theta
            scale2 = 1/(1-4*lam*h*h)
            check('tail_deformation_variance',
                  scale2*(F(1,3)-lam*F(4,3)*h*h) == F(1,3))
            check('tail_deformation_coordinate_lower',
                  scale2*theta*theta <= (1-(1-theta)/3)**2)
            check('tail_deformation_TV_constant',
                  F(8,9)*lam + 3*lam/(1-4*lam*h*h) <= 10*(1-theta))
            # S4 is obtained by shrinking the geometric tail and rescaling.
            T2 = scale2**2*(F(1,15)-(1-theta**4)*F(16,15)*h**4)
            check('tail_deformation_strict_moment_gap', T2 > F(1,15))


def profile_tests(rng: random.Random) -> None:
    for _ in range(160):
        n = rng.randint(2, 18)
        w_raw = [F(1)]
        ratios = [F(rng.randint(2,7), 10) for _ in range(n-1)]
        for r in ratios:
            w_raw.append(w_raw[-1]*r)
        w = [x/sum(w_raw) for x in w_raw]
        u = [F(1)]
        for _ in range(n-1):
            u.append(u[-1]*F(rng.randint(1,10),10))
        z = sum(x*y for x,y in zip(w,u))
        p = [x*y/z for x,y in zip(w,u)]
        D = [sum(p[:k])-sum(w[:k]) for k in range(1,n+1)]
        delta = sum(x*x for x in p)-sum(x*x for x in w)
        d = p[0]-w[0]
        check('profile_energy_identity',
              delta == sum((x-y)**2 for x,y in zip(p,w))
                       + 2*sum((w[k-1]-w[k])*D[k-1] for k in range(1,n)))
        check('profile_head_bound', delta >= 2*(w[0]-w[1])*d)
        for k in range(n):
            check('profile_majorization', D[k] >= 0)
            check('profile_coordinate_bound', abs(p[k]-w[k]) <= d/w[0])


def diagnostic_rows() -> list[dict[str, str | int]]:
    rows = []
    with localcontext() as ctx:
        ctx.prec = 65
        for n in [3,4,6,8,12,20,32]:
            h = Decimal(2)**(-n)
            c = 1/(1-3*h*h).sqrt()
            gap = max((c-1)/2, h*(1-c/2))
            fourth = Decimal(4)/75*h*h*(1-4*h*h)/(1-3*h*h)**2
            rows.append(dict(n=n, h=str(h), scale=str(c),
                spectral_gap=str(gap), fourth_moment_gap=str(fourth),
                TV_upper_bound=str(4*h*h), gap_over_h=str(gap/h),
                moment_gap_over_h_squared=str(fourth/(h*h))))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
        default=Path(__file__).resolve().parents[1]/'results-rerun')
    args = parser.parse_args()
    rng = random.Random(20260930)
    geometric_tests(rng)
    witness_tests()
    profile_tests(rng)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    record = dict(status='PASS', seed=20260930, python=platform.python_version(),
        arithmetic='fractions.Fraction; Decimal diagnostics at precision 65',
        total_exact_assertions=sum(COUNTS.values()), checks=dict(sorted(COUNTS.items())),
        scope='Finite exact regression tests; not formal verification or an analytic proof.')
    (args.output_dir/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    text = '\n'.join([f'Status: {record["status"]}',
        f'Exact assertions: {record["total_exact_assertions"]}',
        f'Python: {record["python"]}', 'Seed: 20260930', '',
        *[f'{name}: {number}' for name,number in sorted(COUNTS.items())], '',record['scope']])+'\n'
    (args.output_dir/'verification.txt').write_text(text)
    rows = diagnostic_rows()
    with (args.output_dir/'witness_diagnostics.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    print(text)
    for row in rows[:5]:
        print(row['n'], *[f'{Decimal(str(row[k])):.7E}' for k in
              ['spectral_gap','fourth_moment_gap','TV_upper_bound']])


if __name__ == '__main__':
    main()
