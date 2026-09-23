#!/usr/bin/env python3
"""Exact finite algebraic regressions for Critical-Point Defects.

These are NOT models of elementary embeddings or measurable cardinals.
They check finite identities only. No third-party dependencies are required.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import random
from typing import Mapping

Series = dict[Fraction, Fraction]


def clean(s: Mapping[Fraction, Fraction]) -> Series:
    return {Fraction(a): Fraction(c) for a, c in s.items() if c}


def add(x: Mapping[Fraction, Fraction], y: Mapping[Fraction, Fraction]) -> Series:
    z = dict(x)
    for a, c in y.items():
        z[a] = z.get(a, Fraction(0)) + c
    return clean(z)


def negate(x: Mapping[Fraction, Fraction]) -> Series:
    return {a: -c for a, c in x.items()}


def multiply(x: Mapping[Fraction, Fraction], y: Mapping[Fraction, Fraction]) -> Series:
    z: Series = {}
    for a, c in x.items():
        for b, d in y.items():
            z[a + b] = z.get(a + b, Fraction(0)) + c * d
    return clean(z)


def reindex(x: Mapping[Fraction, Fraction], scale: Fraction) -> Series:
    if scale <= 0:
        raise ValueError("An order-preserving additive scale must be positive.")
    return {a * scale: c for a, c in x.items()}


def evaluate(x: Mapping[Fraction, Fraction], t: Fraction) -> Fraction:
    if t == 0:
        raise ValueError("Laurent-polynomial evaluation requires nonzero t.")
    if any(a.denominator != 1 for a in x):
        raise ValueError("This finite evaluator requires integral exponents.")
    return sum((c * t ** int(a) for a, c in x.items()), Fraction(0))


def random_laurent(rng: random.Random) -> Series:
    return clean({Fraction(a): Fraction(rng.randint(-4, 4), rng.randint(1, 4))
                  for a in rng.sample(range(-6, 7), rng.randint(0, 7))})


def check_reindexing(rng: random.Random) -> dict[str, int]:
    cases = 500
    leading_checks = 0
    for _ in range(cases):
        x, y, z = (random_laurent(rng) for _ in range(3))
        k = Fraction(rng.randint(1, 7), rng.randint(1, 7))
        assert reindex(add(x, y), k) == add(reindex(x, k), reindex(y, k))
        assert reindex(multiply(x, y), k) == multiply(reindex(x, k), reindex(y, k))
        assert reindex(add(add(x, y), z), k) == add(add(reindex(x, k), reindex(y, k)), reindex(z, k))
        if x:
            leading_checks += 1
            assert max(reindex(x, k)) == k * max(x)
            assert reindex(x, k)[k * max(x)] == x[max(x)]
    return {"cases": cases, "identities_per_case": 3, "leading_term_checked": leading_checks}


def check_deleted_indices(rng: random.Random) -> dict[str, object]:
    """A finite ordered-list deletion analogue, not a finite elementary j."""
    cases = 0
    for n in range(2, 10):
        # Keep index zero, but delete at least one later index.
        for retained_count in range(1, min(n, 5)):
            for suffix in combinations(range(1, n), retained_count - 1):
                retained = {0, *suffix}
                missing = set(range(n)) - retained
                coeffs = [Fraction(rng.choice([-3, -2, -1, 1, 2, 3])) for _ in range(n)]
                full = {Fraction(-i): coeffs[i] for i in range(n)}
                kept = {Fraction(-i): coeffs[i] for i in retained}
                defect = add(full, negate(kept))
                expected = {Fraction(-i): coeffs[i] for i in missing}
                assert defect == expected
                assert not (set(defect) & set(kept))
                assert max(defect) == -min(missing)
                assert defect[max(defect)] == coeffs[min(missing)]
                # Shift the entire defect to strictly positive exponents.
                shifted = {a + (n + 1): c for a, c in defect.items()}
                assert all(a > 0 for a in shifted)
                assert shifted.get(Fraction(0), Fraction(0)) == 0
                first_index = min(missing)
                assert shifted[Fraction(n + 1 - first_index)] == coeffs[first_index]
                cases += 1
    return {"cases": cases, "kind": "finite deletion and shift identities only"}


def check_twisted_product(rng: random.Random) -> dict[str, object]:
    # J and H here are ordinary rational evaluation homomorphisms, not
    # the embeddings of the article. The formal identity is universal.
    cases = 500
    for _ in range(cases):
        x, y = random_laurent(rng), random_laurent(rng)
        jx, jy = evaluate(x, Fraction(2)), evaluate(y, Fraction(2))
        hx, hy = evaluate(x, Fraction(3)), evaluate(y, Fraction(3))
        lhs = evaluate(multiply(x, y), Fraction(2)) - evaluate(multiply(x, y), Fraction(3))
        assert lhs == jx * (jy - hy) + (jx - hx) * hy
    return {"cases": cases, "kind": "universal difference-of-homomorphisms identity"}


def check_boolean_characters() -> dict[str, object]:
    """Exhaust all 2^14 possible maps with empty=0, whole=1 on P(4)."""
    n = 4
    whole = (1 << n) - 1
    accepted: list[list[int]] = []
    for bits in range(1 << (whole - 1)):
        values = [0] + [(bits >> (a - 1)) & 1 for a in range(1, whole)] + [1]
        if any(values[whole ^ a] != 1 - values[a] for a in range(whole + 1)):
            continue
        if any(values[a & b] != values[a] * values[b]
               for a in range(whole + 1) for b in range(whole + 1)):
            continue
        accepted.append(values)
    assert len(accepted) == n
    atoms = []
    for values in accepted:
        selected = [i for i in range(n) if values[1 << i]]
        assert len(selected) == 1
        i = selected[0]
        assert all(values[a] == ((a >> i) & 1) for a in range(whole + 1))
        # Disjoint additivity is checked only on the finite Boolean algebra.
        assert all(values[a | b] == values[a] + values[b]
                   for a in range(whole + 1) for b in range(whole + 1) if not a & b)
        atoms.append(i)
    assert sorted(atoms) == list(range(n))
    return {"points": n, "candidate_maps": 1 << (whole - 1),
            "characters": len(accepted), "all_principal": True,
            "nonprincipal_characters": 0}


def check_hadamard_not_convolution() -> dict[str, object]:
    # The all-one mask is the unit for Hadamard product, not convolution.
    mask = {Fraction(-i): Fraction(1) for i in range(4)}
    hadamard_square = {a: c * c for a, c in mask.items()}
    convolution_square = multiply(mask, mask)
    assert hadamard_square == mask
    assert convolution_square != mask
    assert convolution_square[Fraction(-1)] == 2
    return {"hadamard_unit_identity": True,
            "convolution_is_different": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "finite_regression_results.json")
    args = parser.parse_args()
    rng = random.Random(20260923)
    result = {
        "status": "PASS",
        "seed": 20260923,
        "scope": "Finite algebraic identities only; not a large-cardinal or proof-assistant verification.",
        "reindexing": check_reindexing(rng),
        "deleted_indices": check_deleted_indices(rng),
        "twisted_product": check_twisted_product(rng),
        "boolean_characters": check_boolean_characters(),
        "product_distinction": check_hadamard_not_convolution(),
        "not_tested": ["elementarity of j", "measurability", "class recursion",
                       "canonical normal-form absoluteness", "transfinite strong summation",
                       "supercompactness", "formal correctness of the article"]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
