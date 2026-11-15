#!/usr/bin/env python3
"""Exact finite checks for the rational Basel proof.

The calculations are regression evidence, not a proof of the universal
theorem.  Every assertion uses Fraction or integer arithmetic; decimal
approximations and floating-point comparisons are deliberately absent.

Run: python3 code/check_bounds.py --output validation/exact_checks.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
import time


def prefixes(limit: int) -> dict[str, list[Q]]:
    a, h, o, s = [Q(0)], [Q(0)], [Q(0)], [Q(0)]
    for j in range(limit):
        reciprocal = Q(1, 2 * j + 1)
        a.append(a[-1] + (-1 if j % 2 else 1) * reciprocal)
        h.append(h[-1] + reciprocal)
        o.append(o[-1] + reciprocal * reciprocal)
    for k in range(1, 2 * limit + 18):
        s.append(s[-1] + Q(1, k * k))
    return {"A": a, "H": h, "O": o, "S": s}


def check_one(n: int, p: dict[str, list[Q]], check_rows: bool) -> dict[str, int]:
    a, h, o, s = p["A"], p["H"], p["O"], p["S"]
    triangle = sum(((-1) ** (d - 1) * h[d] / d for d in range(1, n)), Q(0))
    b = [Q(0)] + [(h[n] - h[n - d]) / d for d in range(1, n)]
    error = sum(((-1) ** (d - 1) * b[d] for d in range(1, n)), Q(0))
    boundary = a[n] * a[n] - triangle

    # Exact decomposition by the differences of matrix indices.
    assert a[n] * a[n] == o[n] - triangle + error
    assert all(Q(0) <= b[d] <= b[d + 1] for d in range(n - 1))
    if n > 1:
        assert abs(error) <= b[n - 1]
        assert b[n - 1] == (h[n] - 1) / (n - 1)
        assert b[n - 1] <= h[n] / n
    else:
        assert error == 0

    # Exact triangular convolution and its omitted-row estimate.
    reciprocal_bound = sum(
        (Q(1, (2 * j + 1) * (2 * n - 2 * j - 1)) for j in range(n)),
        Q(0),
    )
    assert reciprocal_bound == h[n] / n
    assert abs(boundary) <= reciprocal_bound
    assert abs(2 * a[n] * a[n] - o[n]) <= 2 * h[n] / n

    row_count = diagonal_count = 0
    if check_rows:
        direct_triangle = Q(0)
        omitted = Q(0)
        for j in range(n):
            aj = Q((-1) ** j, 2 * j + 1)
            row_tail = sum(
                (Q((-1) ** k, 2 * k + 1) for k in range(n - 1 - j, n)),
                Q(0),
            )
            assert abs(row_tail) <= Q(1, 2 * n - 2 * j - 1)
            omitted += aj * row_tail
            direct_triangle += sum(
                (aj * Q((-1) ** k, 2 * k + 1) for k in range(n - 1 - j)),
                Q(0),
            )
            row_count += 1
        assert direct_triangle == triangle
        assert omitted == boundary
        for d in range(1, n):
            diagonal = sum(
                (Q(1, (2 * j + 1) * (2 * d - 2 * j - 1)) for j in range(d)),
                Q(0),
            )
            assert diagonal == h[d] / d
            difference_diagonal = sum(
                (Q(1, (2 * j + 1) * (2 * j + 2 * d + 1)) for j in range(n - d)),
                Q(0),
            )
            assert 2 * difference_diagonal == (h[n - d] + h[d] - h[n]) / d
            diagonal_count += 2

    # Odd/even splitting and the telescoping tail.
    tail = s[2 * n] - s[n]
    assert o[n] == s[2 * n] - s[n] / 4
    assert o[n] == Q(3, 4) * s[n] + tail
    assert Q(1, 4 * n) <= tail <= Q(1, 2 * n)
    assert abs(6 * s[n] - 16 * a[n] * a[n]) <= (16 * h[n] + 4) / n

    uniform_count = 0
    for m in sorted({n, n + 1, n + 7, 2 * n, 2 * n + 17}):
        assert 0 <= s[m] - s[n] <= Q(1, n) - Q(1, m)
        assert abs(o[n] - Q(3, 4) * s[m]) <= Q(1, 2 * n)
        assert abs(6 * s[m] - 16 * a[n] * a[n]) <= (16 * h[n] + 4) / n
        uniform_count += 1

    if n & (n - 1) == 0:
        r = n.bit_length() - 1
        assert h[n] <= 1 + Q(r, 2)
        assert abs(6 * s[n] - 16 * a[n] * a[n]) <= Q(8 * r + 20, n)
        for m in (n, 2 * n, 2 * n + 17):
            assert abs(6 * s[m] - 16 * a[n] * a[n]) <= Q(8 * r + 20, n)

    return {"rows": row_count, "diagonals": diagonal_count, "uniform_samples": uniform_count}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dense", type=int, default=80, help="Check every 1 <= N <= this value.")
    parser.add_argument("--max-power", type=int, default=12, help="Check N=2^r up to this exponent.")
    parser.add_argument("--output", type=Path, help="Write the JSON report here.")
    args = parser.parse_args()
    if args.dense < 1 or args.max_power < 0:
        parser.error("--dense must be positive and --max-power nonnegative")
    started = time.monotonic()
    ns = sorted(set(range(1, args.dense + 1)) | {2**r for r in range(args.max_power + 1)})
    p = prefixes(max(ns))
    totals = {"rows": 0, "diagonals": 0, "uniform_samples": 0}
    for n in ns:
        counts = check_one(n, p, n <= args.dense)
        for key, value in counts.items():
            totals[key] += value

    # The proof of this last inequality is a one-line quantifier-free induction;
    # these independent integer evaluations catch mistakes in its constants.
    for k in range(256):
        assert 16 * k + 76 <= 128 * 2**k
        r = 2 * k + 7
        assert (8 * r + 20) * 2**k <= 2**r
    report = {
        "status": "passed",
        "scope": "finite exact regression checks; not a universal formal proof",
        "arithmetic": "Python integers and fractions.Fraction; no floating-point comparisons",
        "dense_range": [1, args.dense],
        "dyadic_exponents": [0, args.max_power],
        "distinct_N_checked": len(ns),
        "largest_N": max(ns),
        **totals,
        "modulus_integer_samples": 256,
        "checked_claims": [
            "triangular diagonal convolution identity",
            "square decomposition by differences of indices",
            "monotonic tail averages and alternating-sum bound",
            "omitted triangular-row bound",
            "|2 A_N^2 - O_N| <= 2 H_N/N",
            "O_N = S_(2N) - S_N/4",
            "telescoping reciprocal-square tail",
            "|6 S_N - 16 A_N^2| <= (16 H_N+4)/N",
            "uniform |6 S_m - 16 A_N^2| <= (16 H_N+4)/N for sampled m>=N",
            "dyadic H_(2^r) <= 1+r/2",
            "modulus N(k)=2^(2k+7)",
        ],
        "python": sys.version.split()[0],
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
