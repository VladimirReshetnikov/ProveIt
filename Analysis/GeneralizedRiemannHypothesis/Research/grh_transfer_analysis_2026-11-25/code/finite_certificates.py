#!/usr/bin/env python3
"""Exact, bounded checks supporting the GRH transfer report.

Only Python's standard library is required. These checks are not a proof of
GRH, a full Lean check, or a proof that no idoneal integer exceeds the bound.
The connection between reduced forms and ideal classes uses classical Gauss
reduction theory, as explained in the report.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
from math import gcd, isqrt
from pathlib import Path

EULER_LIST = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22,
    24, 25, 28, 30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72,
    78, 85, 88, 93, 102, 105, 112, 120, 130, 133, 165, 168, 177,
    190, 210, 232, 240, 253, 273, 280, 312, 330, 345, 357, 385,
    408, 462, 520, 760, 840, 1320, 1365, 1848,
]


def reduced_forms(discriminant: int):
    """All canonical primitive positive reduced forms of discriminant D<0."""
    assert discriminant < 0 and discriminant % 4 in (0, 1)
    # |b|<=a<=c implies |D|=4ac-b^2 >= 3a^2.
    for a in range(1, isqrt((-discriminant) // 3) + 1):
        for b in range(-a, a + 1):
            numerator = b * b - discriminant
            if numerator % (4 * a):
                continue
            c = numerator // (4 * a)
            if a > c or gcd(gcd(a, b), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            yield (a, b, c)


def ambiguous(form):
    a, b, c = form
    return b == 0 or abs(b) == a or a == c


def idoneal_certificates(limit: int):
    accepted, rejected = [], []
    for n in range(1, limit + 1):
        forms = []
        for form in reduced_forms(-4 * n):
            if not ambiguous(form):
                rejected.append({"n": n, "nonambiguous_reduced_form": form})
                break
            forms.append(form)
        else:
            assert forms
            accepted.append({"n": n, "class_number": len(forms), "all_reduced_forms": forms})
    expected = [n for n in EULER_LIST if n <= limit]
    # This assertion checks our finite result against the reported list;
    # it does not assume that the list is globally exhaustive.
    assert [row["n"] for row in accepted] == expected
    assert len(accepted) + len(rejected) == limit
    return accepted, rejected


def compose(g, h):
    return tuple(g[h[i]] for i in range(3))


def sign(g):
    inversions = sum(g[i] > g[j] for i in range(3) for j in range(i + 1, 3))
    return (-1) ** inversions


def trace_standard(g):
    return sum(g[i] == i for i in range(3)) - 1


def s3_certificate():
    group = list(itertools.permutations(range(3)))
    identity = (0, 1, 2)
    rows = []
    for g in group:
        t, eps = trace_standard(g), sign(g)
        assert t * t == 1 + eps + t
        power = identity
        for k in range(1, 7):
            power = compose(power, g)
            tk, ek = trace_standard(power), sign(power)
            assert tk * tk == 1 + ek + tk
            assert tk * tk in (0, 1, 4)
            for quadratic_value in (-1, 0, 1):
                assert tk * tk * (1 - quadratic_value**k) >= 0
        rows.append({"permutation": g, "trace_rho": t, "epsilon": eps,
                     "trace_tensor": t * t})
    # Character inner products show the three summands occur once.
    for character in (lambda g: 1, sign, trace_standard):
        inner = sum(trace_standard(g)**2 * character(g) for g in group)
        assert inner == len(group)
    # Standard representation is irreducible, dimension two, hence is
    # not a direct sum of the two one-dimensional S3 characters.
    assert sum(trace_standard(g)**2 for g in group) == len(group)
    assert -4 * (-1)**3 - 27 * (-1)**2 == -23
    assert list(reduced_forms(-23)) == [(1, 1, 6), (2, -1, 3), (2, 1, 3)]
    # Check (X-10)^2 (X-3) = X^3-X-1 modulo 23.
    assert [v % 23 for v in (-300, 160, -23, 1)] == [22, 22, 0, 1]
    return {"polynomial": "X^3-X-1", "discriminant": -23,
            "quadratic_reduced_forms": list(reduced_forms(-23)),
            "s3_characters": rows, "powers_checked": [1, 2, 3, 4, 5, 6]}


def branch_quantifier_certificate():
    u, c = (2, 3), (3, 2)
    assert gcd(*u) == gcd(*c) == 1
    products = [a * b for a, b in zip(u, c)]
    assert gcd(*products) == 6
    assert all(a % 2 == 0 or b % 2 == 0 for a, b in zip(u, c))
    return {"U": u, "C": c, "gcd_U": 1, "gcd_C": 1,
            "gcd_pointwise_products": 6, "surviving_prime": 2}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10000)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    assert 1 <= args.limit <= 10000, "This artifact is scoped to the documented bound."
    args.out.mkdir(parents=True, exist_ok=True)
    accepted, rejected = idoneal_certificates(args.limit)
    result = {
        "scope": "Exact finite arithmetic only; no infinite classification or GRH proof",
        "idoneal_bound_inclusive": args.limit,
        "idoneal_count": len(accepted),
        "idoneal_numbers": [row["n"] for row in accepted],
        "s3": s3_certificate(),
        "pointwise_witness_quantifiers": branch_quantifier_certificate(),
        "status": "all checks passed",
    }
    (args.out / "finite_checks.json").write_text(json.dumps(result, indent=2) + "\n")
    (args.out / "idoneal_certificates.json").write_text(json.dumps({
        "bound": args.limit, "accepted": accepted, "rejected_witnesses": rejected
    }, separators=(",", ":")) + "\n")
    with (args.out / "idoneal_numbers.csv").open("w", newline="") as output:
        writer = csv.writer(output)
        writer.writerow(["n", "order_discriminant", "class_number"])
        for row in accepted:
            writer.writerow([row["n"], -4 * row["n"], row["class_number"]])
    print(json.dumps({k: result[k] for k in ("status", "idoneal_bound_inclusive",
                                           "idoneal_count", "idoneal_numbers")}, indent=2))


if __name__ == "__main__":
    main()
