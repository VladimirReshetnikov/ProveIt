#!/usr/bin/env python3
"""Reproduce finite certificates for article.tex, using only the standard library.

Run: python verify.py [--output certificate.json]
The proof of each infinite theorem is in the article, not in these tests.
"""
from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import combinations, product
from math import comb
from pathlib import Path

from construction import (
    BASE_SIX, SEED_SIX, WEIGHTS_SIX, TorusConstruction,
    binomial_coefficients, digit_lift, labels,
    separation_certificate, slice_constant, symmetric_progression_free,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_arc_rigidity() -> int:
    tested = 0
    for k in (4, 6, 8, 10):
        for q in (3, 4, 5):
            for length in range(1, 16):
                modulus = q * length
                for start in range(modulus):
                    for step in range(modulus):
                        points = [(start + i * step) % modulus for i in range(k)]
                        bins = [x // length for x in points]
                        tested += 1
                        if bins == bins[::-1]:
                            require(len(set(bins)) == 1, "equal-arc implication failed")
                            differences = [points[i + 1] - points[i] for i in range(k - 1)]
                            require(len(set(differences)) == 1, "real representatives not an AP")
    points = [(4 + 2 * i) % 10 for i in range(4)]
    bins = [x // 5 for x in points]
    require(bins == [0, 1, 1, 0], "two-arc counterexample transcribed incorrectly")
    return tested


def check_nine_copy() -> int:
    tested = 0
    for k in (4, 6, 8):
        for n in range(1, 13):
            # Monotone consecutive blocks of size k-1 give a valid finite
            # interval coloring, with repeated colors and a short direct proof.
            colors = tuple(b // (k - 1) for b in range(n))
            require(symmetric_progression_free(colors, k), "test coloring is invalid")
            palette = max(colors) + 1
            for resolution in (1, 2, 3):
                grid = 9 * n * resolution
                circle_colors = []
                for u in range(grid):
                    cell = u // resolution
                    a, rest = divmod(cell, 3 * n)
                    b, c = divmod(rest, 3)
                    circle_colors.append((3 * a + c) * palette + colors[b])
                for start in range(grid):
                    for step in range(grid):
                        points = [(start + i * step) % grid for i in range(k)]
                        pattern = [circle_colors[x] for x in points]
                        same_cell = len({x // resolution for x in points}) == 1
                        require((pattern == pattern[::-1]) == same_cell,
                                "nine-copy event equivalence failed")
                        tested += 1
    return tested


def check_binomial_and_cube() -> dict[str, int]:
    relations = 0
    cube_relations = 0
    for k in (4, 6, 8):
        c = binomial_coefficients(k)
        require(sum(c) == 0 and c[-1] == -1, "coefficient normalization failed")
        require(sum(x for x in c if x > 0) == 2 ** (k - 2), "positive weight sum")
        for power in range(k - 1):
            require(sum(c[i] * i ** power for i in range(k)) == 0,
                    "finite-difference relation failed")
            relations += 1
    # The upper-set incidence matrix has determinant one after reverse
    # inclusion ordering; explicitly invert it by descending subset recovery.
    for s in (2, 3, 4, 5, 6):
        subsets = list(range(1 << s))
        coeff = {j: ((17 * j + 3) % 23) - 11 for j in subsets}
        sums = {i: sum(coeff[j] for j in subsets if j & i == i) for i in subsets}
        recovered: dict[int, int] = {}
        for i in sorted(subsets, key=int.bit_count, reverse=True):
            recovered[i] = sums[i] - sum(v for j, v in recovered.items() if j & i == i)
        require(recovered == coeff, "cube coefficient recovery failed")
        cube_relations += len(subsets)
    return {"finite_difference_identities": relations,
            "cube_upper_set_coefficients": cube_relations}


def check_membership() -> int:
    tests = 0
    for k in (4, 6):
        colors = tuple(i // (k - 1) for i in range(8))
        r = max(colors) + 1
        m, _ = labels(k, 9 * r)
        alpha = Fraction(1, 2 ** (k - 2) * m)
        model = TorusConstruction.from_coloring(k, colors, alpha)
        for p in (11, 17, 31, 101):
            for n in range(p):
                color = model.color_at(Fraction(n, p))
                left = Fraction(model.label_values[color], m)
                y = Fraction(pow(n, k - 2, p), p)
                direct = left <= y < left + alpha
                require(model.contains(n, p) == direct, "membership formula failed")
                tests += 1
        require(model.reduced_count() > 0, "slice count must be positive")
    return tests


def run() -> dict[str, object]:
    seed_cert = separation_certificate(SEED_SIX, WEIGHTS_SIX, BASE_SIX)
    require(len(seed_cert) == 64, "seed must have 64 distinct ordered images")
    inner = {str(b): sorted((b + 2 * c) % 16 for c in SEED_SIX) for b in SEED_SIX}
    require(sorted(x for row in inner.values() for x in row) == list(range(16)),
            "inner translates must partition all residues")

    lifts = []
    for t in (1, 2, 3):
        values = digit_lift(SEED_SIX, BASE_SIX, t)
        cert = separation_certificate(values, WEIGHTS_SIX, BASE_SIX ** t)
        require(len(values) == 4 ** t, "wrong lifted cardinality")
        require(max(values) == 13 * (80 ** t - 1) // 79, "wrong maximum")
        lifts.append({"layers": t, "alphabet_size": len(values),
                      "modulus": BASE_SIX ** t, "ordered_tuples": len(cert)})
    require(Fraction(16640, 79) < 211 < 256, "all-moduli constant comparison failed")

    for k, w in ((4, (1, 3)), (6, WEIGHTS_SIX)):
        for size in (1, 2, 3, 4, 5, 7, 8, 15, 16, 17, 31, 32):
            m, values = labels(k, size)
            separation_certificate(values, w, m)

    v4, v6 = slice_constant(4), slice_constant(6)
    require(v4 == Fraction(8, 27), "four-term slice constant failed")
    require(v6 == Fraction(3113, 37500), "six-term slice constant failed")

    def val(n: int, p: int) -> int:
        v = 0
        while n % p == 0:
            n //= p
            v += 1
        return v
    valuation_patterns = {str(p): [val(w, p) for w in WEIGHTS_SIX]
                          for p in (2, 3, 5, 7, 11)}
    require(all(len(set(v)) < 3 for v in valuation_patterns.values()),
            "six-weight valuation pattern failed")

    with localcontext() as ctx:
        ctx.prec = 60
        b = Decimal(80).ln() / Decimal(4).ln()
        theta = 5 + 9 / b
        decimals = {"b6": str(b), "theta6": str(theta), "growth_power": str(1 / b)}

    return {
        "status": "all finite checks passed",
        "limitations": [
            "These tests are not a Lean formalization or a proof of all infinite assertions.",
            "No optimality or exhaustive literature-priority claim is made.",
            "The Shi--Dong coloring family is a credited mathematical input, not generated here.",
        ],
        "seed": {"base": BASE_SIX, "digits": list(SEED_SIX),
                 "weights": list(WEIGHTS_SIX), "ordered_images": seed_cert,
                 "inner_partition_mod_16": inner},
        "lift_checks": lifts,
        "arc_progressions_checked": check_arc_rigidity(),
        "nine_copy_progressions_checked": check_nine_copy(),
        "slice_constants": {"V4": str(v4), "V6": str(v6)},
        "coefficient_checks": check_binomial_and_cube(),
        "membership_checks": check_membership(),
        "valuation_patterns": valuation_patterns,
        "reported_decimals": decimals,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("certificate.json"))
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"])
    print(f"Seed images: {len(result['seed']['ordered_images'])}")
    print(f"Arc progressions: {result['arc_progressions_checked']}")
    print(f"Nine-copy progressions: {result['nine_copy_progressions_checked']}")
    print(f"Exact slices: {result['slice_constants']}")
    print(f"Certificate: {args.output.resolve()}")


if __name__ == "__main__":
    main()
