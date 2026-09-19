#!/usr/bin/env python3
"""Exact checks accompanying the higher-order Stirling log-concavity article.

Python >= 3.9, standard library only. Integer recurrence computations and an
independent rational generating-function computation; no floating-point tests.
Finite tests are regression checks, not substitutes for the proofs.

Usage:
    python verify.py                    # rows through n=200
    python verify.py --max-n 500
    python verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import json
from math import comb, factorial, prod
from pathlib import Path
import sys
from typing import Iterator, List, Dict, Any


def falling(t: int, d: int) -> int:
    """Falling factorial; the empty product is 1."""
    if d < 0:
        raise ValueError("d must be nonnegative")
    return prod(t - j for j in range(d))


def triangle_rows(r: int, kind: str, max_n: int) -> Iterator[List[int]]:
    """Yield rows 0..max_n, including the zero column, using O(max_n) entries."""
    if r < 1 or max_n < 0 or kind not in ("subset", "cycle"):
        raise ValueError("expected r>=1, max_n>=0, kind='subset' or 'cycle'")
    d = r - 1
    previous = [1]
    yield previous
    for n in range(1, max_n + 1):
        row = [0] * (n + 1)
        for k in range(1, n + 1):
            t = n + d * k - 1
            a = comb(t, d) if kind == "subset" else falling(t, d)
            b = k if kind == "subset" else t
            row[k] = a * previous[k - 1]
            if k < n:
                row[k] += b * previous[k]
        yield row
        previous = row


def gf_entry(r: int, kind: str, n: int, k: int) -> int:
    """Independent coefficient extraction from f_r(z)^k or g_r(z)^k.

    The truncation degree is n-k. Multiplication uses rational convolution,
    not a Stirling-number recurrence.
    """
    if k < 0 or k > n:
        return 0
    if k == 0:
        return int(n == 0)
    degree = n - k
    if kind == "subset":
        base = [Fraction(1, factorial(r + j)) for j in range(degree + 1)]
    elif kind == "cycle":
        base = [Fraction(1, r + j) for j in range(degree + 1)]
    else:
        raise ValueError("unknown kind")
    power = [Fraction(1)] + [Fraction(0)] * degree
    for _ in range(k):
        power = [sum((power[i] * base[j - i] for i in range(j + 1)),
                     Fraction(0)) for j in range(degree + 1)]
    result = power[degree] * Fraction(factorial(n + (r - 1) * k), factorial(k))
    if result.denominator != 1:
        raise AssertionError("coefficient formula did not produce an integer")
    return result.numerator


def check(condition: bool, message: str) -> None:
    # Do not use assert: these checks must still run under python -O.
    if not condition:
        raise AssertionError(message)


def check_triangle(r: int, kind: str, max_n: int) -> Dict[str, Any]:
    inequalities = 0
    margins_checked = 0
    previous: List[int] = []
    for n, row in enumerate(triangle_rows(r, kind, max_n)):
        if n > 0:
            check(row[0] == 0 and all(v > 0 for v in row[1:]), "support error")
            diagonal = factorial(r * n) // (
                (factorial(r) ** n if kind == "subset" else r ** n) * factorial(n)
            )
            check(row[n] == diagonal, "diagonal formula disagrees")
            first = 1 if kind == "subset" else factorial(n + r - 2)
            check(row[1] == first, "first-column formula disagrees")
        for k in range(2, n):
            delta = row[k] ** 2 - row[k - 1] * row[k + 1]
            check(delta > 0, f"nonpositive Turan difference: {kind}, r={r}, n={n}, k={k}")
            inequalities += 1
            if kind == "subset" and r == 5:
                t = n + 4 * k - 1
                numerator = ((t - 5) * (2 * t*t - 6*t + 9)
                             * (7*t**3 - 31*t*t - 126*t + 1080))
                check(150 * delta >= numerator * previous[k - 1] ** 2,
                      "quantitative fifth-order lower bound failed")
                margins_checked += 1
        previous = row
    return {
        "kind": kind, "r": r, "max_n": max_n,
        "strict_interior_inequalities_checked": inequalities,
        "quantitative_lower_bounds_checked": margins_checked,
        "status": "passed",
        "proof_in_article": not (kind == "cycle" and r == 5),
    }


def first_failure(r: int, kind: str, max_n: int = 10) -> Dict[str, Any]:
    for n, row in enumerate(triangle_rows(r, kind, max_n)):
        for k in range(2, n):
            delta = row[k] ** 2 - row[k - 1] * row[k + 1]
            if delta < 0:
                return {"r": r, "kind": kind, "n": n, "k": k,
                        "left": row[k-1], "center": row[k], "right": row[k+1],
                        "difference": delta}
    raise AssertionError(f"expected counterexample not found for {kind}, r={r}")


def operator_obstruction() -> Dict[str, Any]:
    """An LC input not mapped to an LC output by the r=5 cycle row operator.

    This input is NOT a Stirling row and does NOT disprove the cycle conjecture.
    """
    n, d, q = 5, 4, 7350
    x = [0] + [q ** (j - 1) for j in range(1, n)] + [0]
    y = [0] * (n + 1)
    for k in range(1, n + 1):
        t = n + d * k - 1
        y[k] = falling(t, d) * x[k-1] + t * x[k]
    check(all(x[k] ** 2 >= x[k-1] * x[k+1] for k in range(1, n)),
          "obstruction input is not LC")
    delta = y[3] ** 2 - y[2] * y[4]
    check(delta < 0, "operator obstruction failed")
    # At t=16, u=x_2=q, v=x_3=q^2, and all three slacks vanish.
    t = 16
    A = falling(t, d)**2 - falling(t-d, d)*falling(t+d, d)
    M = -32*(t-2)*(2*t*t+4*t-51)
    check(delta == q*q*(A + M*q + 16*q*q), "obstruction formula mismatch")
    return {"n": n, "r": 5, "k": 3, "q": q, "input": x, "output": y,
            "difference": delta,
            "interpretation": "failure of universal row-operator preservation, not of the Stirling conjecture"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=200)
    parser.add_argument("--gf-max-n", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path("data/verification.json"))
    args = parser.parse_args()
    if args.max_n < 4 or args.gf_max_n < 4:
        parser.error("both maximum row indices must be at least 4")
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    checks = [check_triangle(r, kind, args.max_n)
              for kind in ("subset", "cycle") for r in range(1, 6)]
    gf_count = 0
    for kind in ("subset", "cycle"):
        for r in range(1, 9):
            for n, row in enumerate(triangle_rows(r, kind, args.gf_max_n)):
                for k, value in enumerate(row):
                    check(value == gf_entry(r, kind, n, k),
                          f"GF disagreement: {kind}, r={r}, n={n}, k={k}")
                    gf_count += 1
    failures = [first_failure(r, "subset") for r in range(6, 13)]
    check(failures[0]["n"] == 4 and failures[0]["difference"] == -1010295,
          "sixth-order counterexample mismatch")
    check(all(f["n"] == 3 for f in failures[1:]), "row-three failures mismatch")
    report = {
        "arithmetic": "exact Python integers and fractions.Fraction",
        "finite_checks_are_not_proofs": True,
        "triangles": checks,
        "total_strict_interior_inequalities": sum(
            c["strict_interior_inequalities_checked"] for c in checks),
        "independent_gf_entries_checked": gf_count,
        "gf_max_n": args.gf_max_n,
        "counterexamples": failures,
        "cycle_order_five_operator_obstruction": operator_obstruction(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    data_dir = args.output.parent
    with (data_dir / "small_rows.csv").open("w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file)
        writer.writerow(["kind", "r", "n", "k", "value"])
        for kind in ("subset", "cycle"):
            for r in range(1, 9):
                for n, row in enumerate(triangle_rows(r, kind, 12)):
                    writer.writerows((kind, r, n, k, value) for k, value in enumerate(row))
    with (data_dir / "row_sums.csv").open("w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file)
        writer.writerow(["kind", "r", "n", "row_sum"])
        for kind in ("subset", "cycle"):
            for r in range(1, 9):
                writer.writerows((kind, r, n, sum(row))
                                 for n, row in enumerate(triangle_rows(r, kind, 30)))
    print(f"PASS: {report['total_strict_interior_inequalities']:,} strict inequalities")
    print(f"PASS: {gf_count:,} independent generating-function entries")
    print("PASS: all fifth-order subset quantitative lower bounds")
    print("PASS: exact counterexamples and cycle operator obstruction")
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
