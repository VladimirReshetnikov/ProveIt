#!/usr/bin/env python3
"""Independent exact finite checks of the d=1 degeneracy theorem.

Standard library only.  Instead of using the translation-stabilizer proof,
enumerate all ternary slices, evaluate the squarefree moment equations
directly, and match opposite moment vectors for the second cube.
"""
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


def moments(pattern, vertices, subsets, p):
    out = []
    for subset in subsets:
        total = 0
        for coefficient, vertex in zip(pattern, vertices):
            monomial = 1
            for i in subset:
                monomial *= vertex[i]
            total += coefficient * monomial
        out.append(total % p)
    return tuple(out)


def signed_coordinate_divisor(t, p):
    return (any(x in (0, 1, p - 1) for x in t)
            or any(t[i] == t[j] or (t[i] + t[j]) % p == 0
                   for i in range(len(t)) for j in range(i)))


def check(k, p):
    vertices = list(product((0, 1), repeat=k))
    subsets = [tuple(i for i in range(k) if mask >> i & 1)
               for mask in range(1 << k)]
    patterns = list(product((-1, 0, 1), repeat=1 << k))
    parity = tuple((-1) ** sum(e) for e in vertices)
    parity_patterns = {tuple(c * x for x in parity) for c in (-1, 0, 1)}
    lookup = {}
    for pattern in patterns:
        vector = moments(pattern, vertices, subsets, p)
        assert vector not in lookup, "The single-cube moment transform is invertible."
        lookup[vector] = pattern
    nonparity = [pattern for pattern in patterns if pattern not in parity_patterns]
    base, full, extras = set(), set(), []
    for t in product(range(p), repeat=k):
        in_base = signed_coordinate_divisor(t, p)
        if in_base:
            base.add(t)
        shifted = [tuple((x + u) % p for x, u in zip(e, t)) for e in vertices]
        for pattern in nonparity:
            vector = moments(pattern, shifted, subsets, p)
            opposite = tuple((-x) % p for x in vector)
            if opposite in lookup:
                full.add(t)
                if not in_base:
                    extras.append({"translation": t, "first_pattern": pattern,
                                   "second_pattern": lookup[opposite]})
                break
    complement_formula = 1
    for i in range(1, k + 1):
        complement_formula *= p - 2 * i - 1
    assert len(base) == p ** k - complement_formula
    assert base <= full
    actual = 1 - Fraction(p - 1, p) ** k * (1 - Fraction(len(full), p ** k))
    lower = 1 - Fraction(p - 1, p) ** k * Fraction(complement_formula, p ** k)
    affine_patterns = 2 * k * k + 4 * k + 3
    remainder = (3 ** (2 ** k) - affine_patterns) ** 2 // 2
    upper = lower + Fraction(p - 1, p) ** k * Fraction(remainder, p * p)
    assert lower <= actual <= upper
    if k == 1:
        assert actual == Fraction(4, p) - Fraction(3, p * p)
    return {
        "k": k, "prime": p, "ternary_slice_patterns": len(patterns),
        "translation_count": p ** k,
        "signed_coordinate_divisor_count": len(base),
        "full_degenerate_translation_count": len(full),
        "extra_translation_count": len(extras),
        "extra_witnesses": extras[:3],
        "actual_degeneracy_proportion": str(actual),
        "theorem_lower_bound": str(lower),
        "theorem_upper_bound": str(upper),
        "checks_passed": True,
    }


if __name__ == "__main__":
    cases = [(1, 5), (1, 7), (1, 11), (2, 7), (2, 11), (2, 13), (2, 17)]
    report = {
        "method": "Direct enumeration and matching of squarefree moment vectors",
        "scope": "Finite checks; the general theorem is proved separately",
        "cases": [check(k, p) for k, p in cases],
    }
    path = Path(__file__).resolve().parents[1] / "data" / "two_cube_verification.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
