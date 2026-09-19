#!/usr/bin/env python3
"""Independent exact verification; Python 3.9+, standard library only.

Polynomial coefficient arrays are in ascending order. No floating-point
arithmetic, fitted recurrences, or computer algebra are used in this file.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import List

ROOT = Path(__file__).resolve().parents[1]


def series_coefficients(p: List[int], q: List[int], count: int) -> List[int]:
    """Expand p(t)/q(t) by exact coefficient comparison, with q[0] = 1."""
    if not q or q[0] != 1:
        raise ValueError("The denominator must have constant coefficient 1.")
    a: List[int] = []
    for k in range(count):
        value = p[k] if k < len(p) else 0
        value -= sum(q[j] * a[k-j] for j in range(1, min(k+1, len(q))))
        a.append(value)
    return a


def add_product(target: List[int], left: List[int], right: List[int],
                shift: int, scale: int) -> None:
    """target += scale * t**shift * left * right, truncated to target length."""
    limit = len(target) - shift
    if limit <= 0:
        return
    for i, x in enumerate(left[:limit]):
        if x:
            for j, y in enumerate(right[:limit-i]):
                if y:
                    target[shift+i+j] += scale*x*y


def reversed_triangle(max_n: int, max_d: int, max_k: int):
    """Compute leading coefficients directly from the original E_n recurrence.

    R[n][d] is t**(d*(n-d-1)) [x**d] E_n(x,1/t), truncated after t**max_k.
    The exceptional empty permutation has R[0][0] = 1.
    No spectral information or proposed rational formula enters this algorithm.
    """
    if min(max_n, max_d, max_k) < 0:
        raise ValueError("Bounds must be nonnegative.")
    rows = [[[1]]]
    for n in range(1, max_n+1):
        row = [[1]]
        for d in range(1, min(max_d, n-1)+1):
            degree = d*(n-d-1)
            value = [0]*(min(max_k, degree)+1)
            if d < len(rows[n-1]):
                previous = rows[n-1][d]
                value[:len(previous)] = previous
            for i in range(1, n):
                m = n-i-1
                scale = math.comb(n-1, i)
                for a in range(min(d-1, i-1)+1):
                    b = d-1-a
                    if a >= len(rows[i]) or b >= len(rows[m]):
                        continue
                    left_degree = a*(i-a-1)
                    right_degree = b*(m-b-1) if m else 0
                    shift = degree-left_degree-right_degree-b
                    if shift < 0:
                        raise AssertionError("The proved degree bound failed.")
                    add_product(value, rows[i][a], rows[m][b], shift, scale)
            row.append(value)
        rows.append(row)
    return rows


def fibonacci(n: int) -> int:
    """Exact fast doubling."""
    if n < 0:
        raise ValueError("Fibonacci index must be nonnegative.")
    def pair(k):
        if k == 0:
            return (0, 1)
        a, b = pair(k//2)
        c = a*(2*b-a)
        e = a*a+b*b
        return (e, c+e) if k % 2 else (c, e)
    return pair(n)[0]


def w2_closed(k: int) -> int:
    if k < 0:
        raise ValueError("Index must be nonnegative.")
    m, parity = divmod(k, 2)
    return ((81 if parity else 45)*3**m + 8*2**m
            - fibonacci(k+10) + m + 3 + parity)


def partition_triangle(max_n: int, max_d: int):
    """T(n,d) = sum_l p_l(n) binom(l,d), with equal-part slots distinguished."""
    p = [[0]*(max_n+1) for _ in range(max_n+1)]
    p[0][0] = 1
    for size in range(1, max_n+1):
        for total in range(size, max_n+1):
            for length in range(1, total+1):
                p[total][length] += p[total-size][length-1]
    return [[sum(p[n][length]*math.comb(length, d)
                 for length in range(d, n+1))
             for d in range(max_d+1)] for n in range(max_n+1)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=40,
                        help="Largest tail deficit checked against E_n (default: 40).")
    parser.add_argument("--export-count", type=int, default=251,
                        help="Number of coefficients saved in CSV and b-files.")
    args = parser.parse_args()
    if args.max_k < 0 or args.export_count < args.max_k+1:
        parser.error("Require max-k >= 0 and export-count > max-k.")
    records = json.loads((ROOT/"data/rational_series.json").read_text())
    max_d = max(record["d"] for record in records)
    max_n = max_d+args.max_k+2
    rows = reversed_triangle(max_n, max_d, args.max_k)
    checks = 0
    all_coeffs = {}
    for record in records:
        d = record["d"]
        a = series_coefficients(record["P"], record["Q"], args.export_count)
        all_coeffs[d] = a
        assert all(x >= 0 for x in a)
        for k in range(args.max_k+1):
            first_stable_n = d+k+1
            assert rows[first_stable_n][d][k] == a[k], (d, k, "boundary")
            assert rows[first_stable_n+1][d][k] == a[k], (d, k, "next row")
            assert rows[max_n][d][k] == a[k], (d, k, "last row")
            checks += 3
        if d == 1:
            assert a == [2**(k+1)-1 for k in range(args.export_count)]
        if d == 2:
            assert a == [w2_closed(k) for k in range(args.export_count)]
        (ROOT/f"data/W{d}_coefficients.txt").write_text(
            "# k  [t^k] W_%d(t)\n" % d
            + "".join(f"{k} {v}\n" for k, v in enumerate(a)))
        print(f"W_{d}: exact agreement for 0 <= k <= {args.max_k}; "
              f"{len(record['Q'])-1}-term recurrence.", flush=True)
    t = partition_triangle(args.max_k+max_d, max_d)
    with (ROOT/"data/coefficients.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["k"]+[f"W{d}" for d in range(1, max_d+1)])
        for k in range(args.export_count):
            writer.writerow([k]+[all_coeffs[d][k] for d in range(1, max_d+1)])
    with (ROOT/"data/partition_comparison.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["d", "k", "W_d[k]", "T(d+k,d)", "difference"])
        for d in range(1, max_d+1):
            for k in range(args.max_k+1):
                v, p = all_coeffs[d][k], t[d+k][d]
                writer.writerow([d, k, v, p, v-p])
    report = {
        "status": "all assertions passed", "max_d": max_d,
        "max_k_checked_against_original_recurrence": args.max_k,
        "largest_n_computed": max_n,
        "independent_integer_comparisons": checks,
        "exported_coefficients_per_series": args.export_count,
        "arithmetic": "Python arbitrary-precision integers; no floating point",
        "formal_proof_assistant_used": False,
    }
    (ROOT/"data/verification.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
