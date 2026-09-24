#!/usr/bin/env python3
"""Reproduce finite checks and generated data. These checks are not the proof.

Run from any directory:
    python code/verify.py
Optional faster run:
    python code/verify.py --limit 100000 --general-limit 10000 --large-records 100
All mathematical checks use exact integers. No third-party dependencies.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
import time
from itertools import islice
from math import isqrt
from pathlib import Path
from record_walk import EvenTraceWalk

ROOT = Path(__file__).resolve().parent.parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def source_recurrence(count: int) -> list[int]:
    """The four-line conjectural recurrence, independent of the lift formula."""
    r = [0]
    while len(r) < count:
        q = (len(r)-1)//4
        base = r[4*q]
        prior = 0 if q == 0 else r[4*q-1]
        b = 2*base + prior + 1
        c = b + 2*base + 1
        d = c + 2*base + 1
        r.extend((b, c, d, 2*d+base+1))
    return r[:count]


def dense_check(D: int, limit: int) -> dict:
    walk = EvenTraceWalk(D)
    a = D//2
    s = low = high = 0
    actual_records = [(0, 0)]
    # Direct summation is independent of the shrinking evaluation algorithm.
    for n in range(1, limit+1):
        b = a*n+isqrt((a*a-1)*n*n)
        s += 1-2*(b & 1)
        require(walk.value(n) == s, f"S mismatch D={D}, N={n}")
        if s < low or s > high:
            actual_records.append((n, s))
            low, high = min(low, s), max(high, s)
        if n <= 10000:
            f = walk.lift(n)
            require(f == walk.B(walk.B(n)+2), f"lift D={D}, n={n}")
            require(walk.B(f) == (D*D-1)*b-D*n+2*D*D-D-2,
                    f"affine identity D={D}, n={n}")
        if n <= 100 or n % 9973 == 0:
            require(walk.extrema(n) == (low, high), f"extrema D={D}, N={n}")
    predicted = []
    for _, n, value in walk.records():
        if n > limit:
            break
        predicted.append((n, value))
    require(actual_records == predicted, f"first-passage mismatch D={D}")
    require(walk.value(0) == 0, "zero convention")
    require(walk.extrema(limit) == (low, high), "final extrema")
    return {"D": D, "through_N": limit, "all_walk_values_match": True,
            "all_records_match": True, "record_count_including_zero": len(predicted),
            "minimum": low, "maximum": high,
            "records": [{"position": n, "S": v} for n, v in predicted]}


def large_check(D: int, count: int) -> dict:
    walk = EvenTraceWalk(D)
    data = list(islice(walk.records(), count))
    largest_digits = 0
    for j, n, expected in data:
        require(walk.value(n) == expected, f"large endpoint D={D}, j={j}")
        require(walk.record(j) == (n, expected), "indexed record")
        if n:
            direction = 1 if expected > 0 else -1
            require(walk.value(n-1) == expected-direction, "record predecessor")
        if j >= D:
            require(walk.lift(data[j-D][1]) == n, "lift on large records")
        if j >= 2*D:
            require(n == (D*D-2)*data[j-D][1]-data[j-2*D][1]+2*(D-1),
                    "scalar recurrence")
        largest_digits = max(largest_digits, len(str(n)))
    return {"D": D, "record_count": count, "max_decimal_digits": largest_digits,
            "all_endpoint_predecessor_and_recurrence_checks_pass": True,
            "method": "exact shrinking recurrence, not direct summation to huge endpoints"}


def write_data() -> None:
    data = ROOT/"data"
    data.mkdir(exist_ok=True)
    walk = EvenTraceWalk(4)
    with (data/"sqrt3_records.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(("record_index", "position", "S_at_record"))
        w.writerows(islice(walk.records(), 1001))
    with (data/"sqrt3_walk_prefix.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(("N", "increment", "S", "running_min", "running_max"))
        s = lo = hi = 0
        w.writerow((0, 0, 0, 0, 0))
        for n in range(1, 20001):
            step = 1-2*(isqrt(3*n*n)&1)
            s += step
            lo, hi = min(lo, s), max(hi, s)
            w.writerow((n, step, s, lo, hi))
    with (data/"even_trace_records.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(("D", "record_index", "position", "S_at_record"))
        for D in range(4, 22, 2):
            w.writerows((D, *row) for row in islice(EvenTraceWalk(D).records(), 101))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=2000000)
    parser.add_argument("--general-limit", type=int, default=50000)
    parser.add_argument("--large-records", type=int, default=1001)
    args = parser.parse_args()
    require(min(args.limit, args.general_limit, args.large_records) > 0,
            "test limits must be positive")
    start = time.perf_counter()
    results = {"python": sys.version, "platform": platform.platform(),
               "arithmetic": "exact Python integers and math.isqrt", "dense": [], "large": []}
    for D in range(4, 22, 2):
        limit = args.limit if D == 4 else args.general_limit
        result = dense_check(D, limit)
        results["dense"].append(result)
        print(f"PASS dense D={D}: all N=0..{limit}, all record positions", flush=True)
    for D in (4, 6, 10, 20):
        count = args.large_records if D == 4 else min(301, args.large_records)
        result = large_check(D, count)
        results["large"].append(result)
        print(f"PASS large D={D}: {count} records, up to {result['max_decimal_digits']} digits",
              flush=True)
    records = [n for _, n, _ in islice(EvenTraceWalk(4).records(), args.large_records)]
    require(records == source_recurrence(len(records)), "source four-line recurrence")
    # Multiply the proposed ordinary generating function by its denominator.
    # (1-z)(1-14*z^4+z^8), numerator z+z^2+z^3+4*z^4-3*z^5+z^6+z^7.
    denominator = {0: 1, 1: -1, 4: -14, 5: 14, 8: 1, 9: -1}
    numerator = {1: 1, 2: 1, 3: 1, 4: 4, 5: -3, 6: 1, 7: 1}
    for n in range(len(records)):
        coefficient = sum(c*records[n-j] for j, c in denominator.items() if j <= n)
        require(coefficient == numerator.get(n, 0), f"generating function coefficient {n}")
    for D in range(4, 22, 2):
        vals = [n for _, n, _ in islice(EvenTraceWalk(D).records(), 301)]
        trace = D*D-2
        den = {0: 1, 1: -1, D: -trace, D+1: trace, 2*D: 1, 2*D+1: -1}
        num = {j: 1 for j in range(1, D)}
        num.update({D: D, D+1: -(D-1)})
        num.update({j: 1 for j in range(D+2, 2*D)})
        for n in range(len(vals)):
            require(sum(c*vals[n-j] for j, c in den.items() if j <= n) == num.get(n, 0),
                    f"general generating function D={D}, n={n}")
    for D in (0, 2, 3, 5):
        try:
            EvenTraceWalk(D)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid D accepted")
    write_data()
    results.update({"source_recurrence_terms_checked": len(records),
                    "generating_function_coefficients_checked": len(records),
                    "general_generating_function_coefficients_per_D": 301,
                    "all_passed": True,
                    "elapsed_seconds": round(time.perf_counter()-start, 3),
                    "limitations": "Finite tests corroborate, but do not replace, the proofs. "
                    "Very large endpoints were checked by the proved shrinking recurrence."})
    (ROOT/"data"/"verification.json").write_text(json.dumps(results, indent=2)+"\n")
    print(f"ALL CHECKS PASSED in {results['elapsed_seconds']} seconds", flush=True)


if __name__ == "__main__":
    main()
