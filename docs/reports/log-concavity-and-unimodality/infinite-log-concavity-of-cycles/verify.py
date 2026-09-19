#!/usr/bin/env python3
"""Exact, dependency-free verification of the cycle classification.

Python 3.10+; no floating-point arithmetic is used. Integers in the JSON
certificate are encoded as decimal strings to avoid lossy JSON readers.
The proof for arbitrarily large n is symbolic in article.tex, not an
inference from this finite test. Run derive_symbolic.py for an additional
(optional SymPy) check of the identities used in that proof.
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
from fractions import Fraction
from math import comb
from pathlib import Path
from typing import Sequence, TypeVar

Number = TypeVar("Number", int, Fraction)


def require(condition: bool, message: str) -> None:
    """Unlike an assert statement, this check is not disabled by python -O."""
    if not condition:
        raise AssertionError(message)


def cycle_row(n: int) -> list[int]:
    if not isinstance(n, int) or n < 3:
        raise ValueError("A simple cycle must have an integer n >= 3.")
    return [0, n - 1] + [comb(n, k) for k in range(2, n + 1)]


def log_operator(a: Sequence[int]) -> list[int]:
    """L(a)_k = a_k^2 - a_(k-1)*a_(k+1), with zero padding."""
    if not a:
        raise ValueError("The sequence must not be empty.")
    padded = [0, *a, 0]
    return [padded[k + 1] ** 2 - padded[k] * padded[k + 2]
            for k in range(len(a))]


def known_prefix_operator(a: Sequence[Number]) -> list[Number]:
    """Compute only entries justified by a known prefix, not a right zero."""
    if len(a) < 2:
        raise ValueError("The prefix must contain at least two entries.")
    return [a[k] ** 2 - (a[k - 1] * a[k + 1] if k else 0)
            for k in range(len(a) - 1)]


def min_ratio(a: Sequence[int]) -> tuple[Fraction, int]:
    require(all(x >= 0 for x in a), "Ratio certificate needs nonnegative data.")
    ratios = [(Fraction(a[k] ** 2, a[k - 1] * a[k + 1]), k)
              for k in range(1, len(a) - 1)
              if a[k - 1] * a[k + 1] > 0]
    if not ratios:
        raise ValueError("No nonzero neighboring product.")
    return min(ratios)


def in_three_cone(a: Sequence[int]) -> bool:
    return all(x >= 0 for x in a) and all(
        a[k] ** 2 >= 3 * a[k - 1] * a[k + 1]
        for k in range(1, len(a) - 1))


def q_polynomial(n: int) -> int:
    return 2*n**4 - 12*n**3 - 327*n**2 - 412*n + 36


def third_entry_two(n: int) -> int:
    num = -n**3 * (n - 1)**8 * (n + 4) * q_polynomial(n)
    require(num % 103680 == 0, f"Nonintegral witness at n={n}.")
    return num // 103680


EXPECTED_CONES = {
    3: (0, 2, Fraction(9, 2)),
    4: (1, 3, Fraction(25, 6)),
    5: (2, 3, Fraction(256, 49)),
    6: (2, 3, Fraction(100, 27)),
    7: (2, 3, Fraction(6845, 2187)),
    8: (3, 3, Fraction(30926, 5863)),
    9: (3, 3, Fraction(8736525, 1666093)),
    10: (3, 3, Fraction(2991871581875, 519958761651)),
    11: (3, 2, Fraction(32433025, 8287488)),
}
EXPECTED_FAILURES = {
    12: (5, -249621701601023742801969101519201265582387397744),
    13: (4, -3618341131654935620812800),
    14: (4, -199158562975246657489530096),
    15: (4, -2734560032125157358883149375),
    16: (4, -25982668618402950000000000000),
    17: (3, -28272276537344),
}


def analyze_cycle(n: int) -> dict:
    a = cycle_row(n)
    rows = [[str(x) for x in a]]
    for depth in range(6):
        negatives = [(k, x) for k, x in enumerate(a) if x < 0]
        if negatives:
            expected_depth = 5 if n == 12 else 4 if n <= 16 else 3
            require(depth == expected_depth, f"Wrong first failure for C_{n}.")
            require(negatives[0][0] == 2, f"Wrong first negative index for C_{n}.")
            if n in EXPECTED_FAILURES:
                require((depth, a[2]) == EXPECTED_FAILURES[n],
                        f"Wrong negative value for C_{n}.")
            return {"n": n, "outcome": "failure", "depth": depth,
                    "negative_entries": [[k, str(x)] for k, x in negatives],
                    "iterates": rows}
        if in_three_cone(a):
            require(n in EXPECTED_CONES, f"Unexpected positive certificate C_{n}.")
            ratio, k = min_ratio(a)
            require((depth, k, ratio) == EXPECTED_CONES[n],
                    f"Incorrect cone certificate C_{n}.")
            require(in_three_cone(log_operator(a)), "Cone invariant check failed.")
            return {"n": n, "outcome": "infinite_by_three_cone", "depth": depth,
                    "minimum_ratio_index": k, "minimum_ratio": str(ratio),
                    "iterates": rows}
        if depth < 5:
            a = log_operator(a)
            rows.append([str(x) for x in a])
    raise AssertionError(f"No conclusion after five iterates for C_{n}.")


def independent_cycle_recurrence(n_max: int) -> None:
    # Absolute coefficients of the deletion-contraction identity:
    # A_n(x) = A_(n-1)(x) + x*(1+x)^(n-1).
    a = [0, 2, 3, 1]  # triangle
    require(a == cycle_row(3), "Triangle base case mismatch.")
    for n in range(4, n_max + 1):
        a = [*a, 0]
        for k in range(1, n + 1):
            a[k] += comb(n - 1, k - 1)
        require(a == cycle_row(n), f"Deletion-contraction mismatch C_{n}.")


def exact_limit_test() -> None:
    # Sufficient prefix of coefficients of exp(x)-1.
    a = [Fraction(0), Fraction(1), Fraction(1, 2), Fraction(1, 6),
         Fraction(1, 24), Fraction(1, 120)]
    for _ in range(3):
        a = known_prefix_operator(a)
    require(a[2] == Fraction(-1, 51840), "Incorrect limiting witness.")


def forward_differences(values: Sequence[int]) -> list[int]:
    row = list(values)
    first = []
    while row:
        first.append(row[0])
        row = [y - x for x, y in zip(row, row[1:])]
    return first


def verify(n_max: int) -> list[dict]:
    if n_max < 17:
        raise ValueError("--max-n must be at least 17.")
    independent_cycle_recurrence(n_max)
    certs = []
    for n in range(3, n_max + 1):
        result = analyze_cycle(n)
        if n <= 17:
            certs.append(result)
        a = cycle_row(n)
        for j in range(1, 4):
            a = log_operator(a)
            if j <= 2:
                require(all(x >= 0 for x in a), f"2-LC failed C_{n}.")
        require(a[2] == third_entry_two(n), f"Formula mismatch C_{n}.")
        require(all(x >= 0 for x in a) == (n <= 16),
                f"3-LC classification mismatch C_{n}.")
    # Large n: test the exact local prefix; no huge full row is constructed.
    for n in [1000, 10000, 10**6, 10**12]:
        a = [0, n - 1] + [comb(n, k) for k in range(2, 6)]
        for _ in range(3):
            a = known_prefix_operator(a)
        require(a[2] == third_entry_two(n), f"Large-n prefix mismatch {n}.")
    exact_limit_test()
    w = [-third_entry_two(17 + m) for m in range(40)]
    diffs = forward_differences(w)
    require(all(x > 0 for x in diffs[:17]), "Nonpositive forward difference.")
    require(all(x == 0 for x in diffs[17:]), "Degree exceeds sixteen.")
    for m in range(40):
        reconstructed = sum(diffs[j] * comb(m, j) for j in range(min(m, 16)+1))
        require(reconstructed == w[m], "Newton interpolation mismatch.")
    return certs


def write_data(out_dir: Path, certs: list[dict]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    envelope = {
        "convention": "Increasing coefficient degree; zero padding; no absolute values after L.",
        "integers": "All sequence values are decimal strings for exact JSON interchange.",
        "certificates": certs,
    }
    (out_dir / "certificates.json").write_text(
        json.dumps(envelope, indent=2) + "\n", encoding="utf-8")
    with (out_dir / "cycle_coefficients.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "degree_k", "absolute_coefficient"])
        for n in range(3, 101):
            writer.writerows((n, k, x) for k, x in enumerate(cycle_row(n)))
    with (out_dir / "third_iteration_witness.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "L3_index_2"])
        writer.writerows((n, third_entry_two(n)) for n in range(3, 101))
    w = [-third_entry_two(17 + m) for m in range(17)]
    diffs = forward_differences(w)
    # P(t)=(1-t)^17 sum_m w_m t^m.
    numerator = [sum((-1)**j * comb(17, j) * w[k-j]
                     for j in range(k+1)) for k in range(17)]
    (out_dir / "witness_generating_function.json").write_text(json.dumps({
        "definition": "w_m = -L^3(a^(17+m))_2, m >= 0",
        "forward_differences_at_0": [str(x) for x in diffs],
        "denominator": "(1-t)^17",
        "numerator_coefficients_in_ascending_degree": [str(x) for x in numerator],
    }, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=200,
                        help="Full-row checks through this n (default: 200).")
    parser.add_argument("--write-data", action="store_true",
                        help="Regenerate the bundled data files.")
    args = parser.parse_args()
    certs = verify(args.max_n)
    if args.write_data:
        write_data(Path(__file__).resolve().parent / "data", certs)
    print(f"PASS: exact full-row checks for C_3 through C_{args.max_n}.")
    print("PASS: all nine invariant-cone certificates, C_3 through C_11.")
    print("PASS: first failures 5,4,4,4,4,3 for C_12 through C_17.")
    print("PASS: third-iterate formula and local tests up to n=10^12.")
    print("PASS: exponential limit, degree-16 witness and generating-function data.")
    print("Universal statements are proved in the article; finite tests alone are not the proof.")
    print(f"Environment: Python {sys.version.split()[0]}, standard library only.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, AssertionError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        sys.exit(1)
