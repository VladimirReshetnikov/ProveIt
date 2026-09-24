#!/usr/bin/env python3
"""Wide-scan exact verification for the canonical binomial decomposition.

This is the second, independent verification stack of the merged package.  It
was written separately from the top-level ``verify.py`` and shares no code with
it: the canonical expansion, the discriminants and the splitting operator are
all reimplemented here, and the colex-prefix routine recomputes the operator by
literal subset enumeration rather than by arithmetic.

All coefficient/root-classification tests use integer or rational arithmetic.
Run from any directory:
    python3 code/verify_wide.py --out results
Optional bounded cubic enumeration: --max-a 14 (the recorded default).
The finite checks do not replace the proofs in the accompanying article.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
from time import perf_counter
from typing import Sequence


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def choose(n: int, k: int) -> int:
    """Binomial coefficients with the nonnegative-index zero convention."""
    if n < 0 or k < 0:
        raise ValueError("Binomial arguments must be nonnegative")
    return comb(n, k) if k <= n else 0


def binomial_expansion(value: int, degree: int) -> list[tuple[int, int]]:
    """Return the unique decreasing-top canonical degree-binomial expansion."""
    if type(value) is not int or type(degree) is not int:
        raise TypeError("value and degree must be integers")
    if value < 0 or degree < 1:
        raise ValueError("Require value >= 0 and degree >= 1")
    remaining = value
    upper: int | None = None
    digits: list[tuple[int, int]] = []
    for k in range(degree, 0, -1):
        if remaining == 0:
            break
        lo = k - 1
        if upper is None:
            hi = k
            while choose(hi, k) <= remaining:
                hi *= 2
        else:
            hi = upper
        require(choose(hi, k) > remaining, "Invalid greedy upper bound")
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if choose(mid, k) <= remaining:
                lo = mid
            else:
                hi = mid
        require(lo >= k, "Greedy digit must be positive")
        digits.append((lo, k))
        remaining -= choose(lo, k)
        upper = lo
    require(remaining == 0, "Canonical expansion failed to terminate")
    return digits


def split_integer(value: int, degree: int) -> tuple[int, int]:
    digits = binomial_expansion(value, degree)
    deletion = sum(choose(a - 1, k) for a, k in digits)
    link = sum(choose(a - 1, k - 1) for a, k in digits)
    require(deletion + link == value, "Pascal identity failed")
    return deletion, link


def split_polynomial(coefficients: Sequence[int]) -> tuple[list[int], list[int]]:
    """Ascending-power coefficient lists; trailing zero entries are retained."""
    if not coefficients or coefficients[0] != 1:
        raise ValueError("The input must have constant coefficient 1")
    if any(type(c) is not int or c < 0 for c in coefficients):
        raise ValueError("Coefficients must be nonnegative integers")
    g, h = [1], []
    for k, value in enumerate(coefficients[1:], 1):
        deletion, link = split_integer(value, k)
        g.append(deletion)
        h.append(link)
    return g, h


def product_linear(weights: Sequence[int], max_degree: int | None = None) -> list[int]:
    coefficients = [1]
    for weight in weights:
        if type(weight) is not int or weight <= 0:
            raise ValueError("Weights must be positive integers")
        coefficients.append(0)
        for i in range(len(coefficients) - 1, 0, -1):
            coefficients[i] += weight * coefficients[i - 1]
        if max_degree is not None:
            coefficients = coefficients[: max_degree + 1]
    return coefficients


def trim(coefficients: Sequence[int]) -> list[int]:
    result = list(coefficients)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def discriminant(coefficients: Sequence[int]) -> int:
    """Degree <= 3. The degree-one convention is 1."""
    c = trim(coefficients)
    if len(c) <= 2:
        return 1
    if len(c) == 3:
        return c[1] ** 2 - 4 * c[2] * c[0]
    if len(c) == 4:
        d, linear, quadratic, cubic = c
        return (quadratic**2 * linear**2 - 4 * cubic * linear**3
                - 4 * quadratic**3 * d - 27 * cubic**2 * d**2
                + 18 * cubic * quadratic * linear * d)
    raise ValueError("This discriminant routine supports degree <= 3")


def determinant(matrix: Sequence[Sequence[int]]) -> Fraction:
    """Independent rational Gaussian elimination for a small determinant."""
    a = [[Fraction(x) for x in row] for row in matrix]
    n = len(a)
    result = Fraction(1)
    for k in range(n):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        p = a[k][k]
        result *= p
        for i in range(k + 1, n):
            q = a[i][k] / p
            for j in range(k + 1, n):
                a[i][j] -= q * a[k][j]
            a[i][k] = Fraction(0)
    return result


def resultant_discriminant(coefficients: Sequence[int]) -> int:
    """Compute disc via the Sylvester determinant of P and P'."""
    p = trim(coefficients)
    n = len(p) - 1
    if n <= 1:
        return 1
    q = [i * p[i] for i in range(1, n + 1)]
    p, q = list(reversed(p)), list(reversed(q))
    size = 2 * n - 1
    rows = []
    for shift in range(n - 1):
        rows.append([0] * shift + p + [0] * (size - shift - len(p)))
    for shift in range(n):
        rows.append([0] * shift + q + [0] * (size - shift - len(q)))
    result = (-1) ** (n * (n - 1) // 2) * determinant(rows) / p[0]
    require(result.denominator == 1, "Nonintegral discriminant")
    return result.numerator


def elementary_23(d: int, n: int) -> tuple[int, int]:
    """Independent power-sum formulas for weights n,...,n+d-1."""
    j1 = d * (d - 1) // 2
    j2 = d * (d - 1) * (2 * d - 1) // 6
    s1 = d * n + j1
    s2 = d * n * n + 2 * n * j1 + j2
    s3 = d * n**3 + 3 * n * n * j1 + 3 * n * j2 + j1**2
    return (s1*s1 - s2) // 2, (s1**3 - 3*s1*s2 + 2*s3) // 6


def example_certificate(weights: list[int]) -> dict:
    f = product_linear(weights)
    g, h = split_polynomial(f)
    for p in [f, g, h]:
        require(discriminant(p) == resultant_discriminant(p),
                "Discriminant disagrees with Sylvester determinant")
    return {
        "weights": weights, "f": f, "g": g, "h": h,
        "binomial_digits": [binomial_expansion(c, k)
                            for k, c in enumerate(f[1:], 1)],
        "disc_f": discriminant(f), "disc_g": discriminant(g),
        "disc_h": discriminant(h),
    }


def enumerate_cubics(max_a: int) -> tuple[list[dict], list[dict], list[dict]]:
    counts, failures, small = [], [], []
    for a in range(1, max_a + 1):
        count = bad_count = tested = 0
        # Necessary AM-GM bounds for the three positive reciprocal roots.
        for b in range(1, a*a // 3 + 1):
            for c in range(1, a**3 // 27 + 1):
                tested += 1
                f = [1, a, b, c]
                if discriminant(f) < 0:
                    continue
                count += 1
                g, h = split_polynomial(f)
                dg, dh = discriminant(g), discriminant(h)
                row = {"A": a, "B": b, "C": c,
                       "disc_f": discriminant(f), "disc_g": dg, "disc_h": dh}
                if a <= 8:
                    small.append(row)
                if dg < 0 or dh < 0:
                    bad_count += 1
                    failures.append({**row, "g": g, "h": h})
        counts.append({"A": a, "candidate_triples": tested,
                       "real_rooted": count, "failures": bad_count})
    return counts, failures, small


def colex_checks(max_vertex: int = 12, max_degree: int = 6) -> int:
    """Count vertex 1 in initial colex segments, independently of the digits."""
    tests = 0
    for degree in range(1, max_degree + 1):
        sets = sorted(combinations(range(1, max_vertex + 1), degree),
                      key=lambda s: tuple(reversed(s)))
        containing = 0
        for value, face in enumerate(sets, 1):
            containing += int(1 in face)
            require(split_integer(value, degree)[1] == containing,
                    f"Colex disagreement at degree={degree}, value={value}")
            tests += 1
    return tests


def complex_certificate() -> dict:
    triangles = set(combinations(range(1, 6), 3))
    triangles |= {tuple(sorted((6,) + pair))
                  for pair in combinations(range(1, 5), 2)}
    triangles |= {(1, 5, 6), (2, 5, 6)}
    faces = {frozenset()}
    faces |= {frozenset((v,)) for v in range(1, 9)}
    faces |= {frozenset(pair) for pair in combinations(range(1, 8), 2)}
    faces |= {frozenset(t) for t in triangles}
    for face in faces:
        for v in face:
            require(face - {v} in faces, "Not a simplicial complex")
    deletion = {s for s in faces if 1 not in s}
    link = {s - {1} for s in faces if 1 in s}
    count = lambda fs: [sum(len(s) == k for s in fs) for k in range(4)]
    f, g, h = count(faces), count(deletion), trim(count(link))
    require(f == [1, 8, 21, 18], "Wrong complex f-vector")
    require((g, h) == split_polynomial(f), "Wrong deletion or link")
    expected_link_edges = {frozenset(e) for e in combinations(range(2, 7), 2)}
    require({s for s in link if len(s) == 2} == expected_link_edges,
            "The link graph is not the stated K5 plus an isolated vertex")
    return {"vertices": list(range(1, 9)),
            "edges": [list(e) for e in combinations(range(1, 8), 2)],
            "triangles": [list(t) for t in sorted(triangles)],
            "f": f, "deletion": g, "link": h}


def write_csv(path: Path, rows: list[dict]) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def run(out: Path, max_a: int) -> dict:
    start = perf_counter()
    out.mkdir(parents=True, exist_ok=True)
    examples = [example_certificate([2, 3, 4]), example_certificate([2, 3, 3])]
    require((examples[0]["g"], examples[0]["h"]) ==
            ([1, 8, 19, 11], [1, 7, 13]), "Wrong main example")
    require([e["disc_g"] for e in examples] == [-31, -59], "Wrong g discs")
    require([e["disc_h"] for e in examples] == [-3, -4], "Wrong h discs")

    expansion_tests = 0
    for k in range(1, 9):
        for value in range(0, 5001):
            digits = binomial_expansion(value, k)
            require(sum(choose(a, j) for a, j in digits) == value,
                    "Expansion reconstruction error")
            require(all(digits[i][0] > digits[i+1][0]
                        for i in range(len(digits)-1)), "Nondecreasing digit")
            split_integer(value, k)
            expansion_tests += 1
    colex_tests = colex_checks()

    quadratic_tests = 0
    for a in range(2, 101):
        for b in range(1, a*a // 4 + 1):
            g, h = split_polynomial([1, a, b])
            require(discriminant(g) >= 0 and discriminant(h) >= 0,
                    "Quadratic preservation failed")
            quadratic_tests += 1

    counts, failures, small = enumerate_cubics(max_a)
    require(not any(r["A"] <= 7 for r in failures), "Smaller cubic failure")
    at_eight = [(r["A"], r["B"], r["C"]) for r in failures if r["A"] == 8]
    if max_a >= 8:
        require(at_eight == [(8, 21, 18)], "Unexpected degree-3 A=8 scan")

    all_degree = []
    for d in range(3, 101):
        for n in (10*d**3, 10*d**3+1, 20*d**3):
            prefix = product_linear(list(range(n, n+d)), max_degree=3)
            e2, e3 = elementary_23(d, n)
            require(prefix[2:] == [e2, e3], "Power-sum disagreement")
            b1, b2 = split_integer(e2, 2)[1], split_integer(e3, 3)[1]
            margin = 2*(d-1)*b2 - (d-2)*b1*b1
            require(margin > 0, "All-degree Newton obstruction failed")
            all_degree.append({"degree": d, "n": n, "e2": e2, "e3": e3,
                               "h1": b1, "h2": b2, "newton_margin": margin})

    complex_data = complex_certificate()
    summary = {
        "status": "all checks passed",
        "python_version": platform.python_version(),
        "max_cubic_A": max_a,
        "expansion_checks": expansion_tests,
        "independent_colex_checks": colex_tests,
        "quadratic_preservation_checks": quadratic_tests,
        "cubic_candidate_triples": sum(r["candidate_triples"] for r in counts),
        "real_rooted_cubics": sum(r["real_rooted"] for r in counts),
        "cubic_failures": len(failures),
        "all_degree_instances": len(all_degree),
        "independent_resultant_discriminants": 6,
        "elapsed_seconds": round(perf_counter() - start, 4),
        "trust_boundary": "Exact computation, not proof-assistant formalization; "
                          "the unbounded theorems are proved in the article.",
    }
    for name, data in [("verification.json", summary), ("examples.json", examples),
                       ("cubic_failures.json", failures),
                       ("compressed_complex.json", complex_data)]:
        (out / name).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    write_csv(out / "cubic_counts.csv", counts)
    write_csv(out / "all_real_rooted_cubics_A_le_8.csv", small)
    write_csv(out / "all_degree_certificates.csv", all_degree)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parent.parent / "results")
    parser.add_argument("--max-a", type=int, default=14)
    args = parser.parse_args()
    if not 1 <= args.max_a <= 100:
        parser.error("--max-a must be between 1 and 100; large bounds are expensive")
    print(json.dumps(run(args.out, args.max_a), indent=2))


if __name__ == "__main__":
    main()
