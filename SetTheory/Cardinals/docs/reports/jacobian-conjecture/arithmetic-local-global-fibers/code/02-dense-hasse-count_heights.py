#!/usr/bin/env python3
"""Reproduce exact target-height counts for completely split Hasse failures.

Integer membership tests use checked int64 arrays; floating-point arithmetic
is confined to displaying asymptotic constants. The default table is modest.
The running time grows linearly in |c|*T, so this is not a large-height solver.
"""
from __future__ import annotations

import argparse
import json
from math import isqrt
from pathlib import Path
import platform
import time

import mpmath as mp
import numpy as np

from split_fibres import factor_integer, integral_exceptions, v2

ROOT = Path(__file__).resolve().parents[1]


def density(c: int):
    """Numerical display of the exact Euler-product formula in the article."""
    if c == 0:
        raise ValueError("The counting theorem assumes c != 0.")
    factors = factor_integer(c)
    e = factors.get(2, 0)
    sigma = (mp.mpf(3)/8 if e == 0 else mp.mpf(3)/16 if e <= 2
             else mp.mpf(3)/mp.mpf(2)**(2*e-1))
    result = sigma*9/mp.pi**2
    for p, exponent in factors.items():
        if p == 2:
            continue
        result *= mp.mpf(3)/mp.mpf(p)**(2*exponent)
        if p >= 5:
            result /= 1-mp.mpf(1)/(p*p)
    return result


def leading_constant(c: int):
    integral = mp.gamma(mp.mpf(1)/3)**2/(2*mp.gamma(mp.mpf(2)/3))
    return integral*mp.mpf(2*c*c)**(mp.mpf(2)/3)*density(c)


def count(c: int, height: int) -> dict:
    """Count targets, not root orderings, with |A|, |B| <= height.

    The quadratic identity in Section 9 gives a complete root bound. The
    six-to-one numerator parametrization is exact away from repeated roots.
    """
    if c == 0 or height < 1:
        raise ValueError("Require c != 0 and an integer height >= 1.")
    M = 2*isqrt(abs(c)*height+2)+4
    # Conservative bounds on every integer array expression below.
    limit = np.iinfo(np.int64).max
    bounds = [M*M*(2+2*M), 3*M*M+4*M, 2*c*c*height,
              abs(c)*height, 2*c*c, 8*M+8]
    if max(bounds) > limit:
        raise ValueError("Requested parameters exceed checked int64 arithmetic.")
    if M > 50_000:
        raise ValueError("This reference enumerator caps the root bound at 50,000.")
    bs = np.arange(-M, M+1, dtype=np.int64)
    ordered_count = 0
    allowed_primes = sorted({2, *factor_integer(c)})
    e = v2(c)
    start = time.perf_counter()
    for a in range(-M, M+1):
        rs = 2-a-bs
        product = a*bs*rs
        pair_sum = 2*(a+bs)-a*a-a*bs-bs*bs
        selected = ((product % (2*c*c) == 0) & (pair_sum % c == 0)
                    & (np.abs(product) <= 2*c*c*height)
                    & (np.abs(pair_sum) <= abs(c)*height)
                    & (a != bs) & (a != rs) & (bs != rs))
        b, r = bs[selected], rs[selected]
        # These are the proved dyadic ROOT conditions, not a floating solver.
        if e == 0:
            root_residues = np.vstack((np.full_like(b, a % 4), b % 4, r % 4))
            root_residues.sort(axis=0)
            good_two = np.all(root_residues == np.array([[1], [2], [3]]), axis=0)
        elif e == 1:
            good_two = ((a % 2 == 0) & (b % 2 == 0)
                        & ((a//2) % 2 + (b//2) % 2 + (r//2) % 2 == 1))
        else:
            good_two = np.ones(b.size, dtype=bool)
        b = b[good_two]
        g = np.gcd(a-b, 3*a-2)
        for p in allowed_primes:
            mask = g % p == 0
            while np.any(mask):
                g[mask] //= p
                mask = g % p == 0
        ordered_count += int(np.count_nonzero(g == 1))
    if ordered_count % 6:
        raise AssertionError("The six-to-one numerator symmetry failed.")
    local_count = ordered_count//6
    exceptions = sorted(target for target in integral_exceptions(c)
                        if abs(target[0]) <= height and abs(target[1]) <= height)
    failures = local_count-len(exceptions)
    kappa = leading_constant(c)
    scale = mp.mpf(height)**(mp.mpf(2)/3)
    return {
        "c": c, "T": height, "root_bound": M,
        "ordered_locally_soluble_numerator_pairs": ordered_count,
        "locally_soluble_split_targets": local_count,
        "globally_integral_exceptions": [list(t) for t in exceptions],
        "integral_hasse_failures": failures,
        "rho": mp.nstr(density(c), 25), "kappa": mp.nstr(kappa, 25),
        "failures_over_T_two_thirds": mp.nstr(failures/scale, 20),
        "ratio_to_asymptotic": mp.nstr(failures/(kappa*scale), 20),
        "elapsed_seconds": round(time.perf_counter()-start, 4),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, nargs="+", default=[1, 2, 3, 4, 8])
    parser.add_argument("--heights", type=int, nargs="+", default=[1000, 10000, 100000])
    parser.add_argument("--output", type=Path, default=ROOT/"data"/"height_counts.json")
    args = parser.parse_args()
    mp.mp.dps = 40
    rows = []
    lines = ["c | T | exact Hasse failures | kappa(c) | N/T^(2/3)"]
    try:
        for c in args.c:
            for height in args.heights:
                row = count(c, height)
                rows.append(row)
                line = (f"{c} | {height} | {row['integral_hasse_failures']} | "
                        f"{float(row['kappa']):.12f} | "
                        f"{float(row['failures_over_T_two_thirds']):.12f}")
                lines.append(line)
                print(line, flush=True)
    except ValueError as error:
        parser.error(str(error))
    report = {"python": platform.python_version(), "numpy": np.__version__,
              "mpmath": mp.__version__, "rows": rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    args.output.with_suffix(".txt").write_text("\n".join(lines)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
