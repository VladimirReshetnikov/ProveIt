#!/usr/bin/env python3
"""Exact finite checks for Infinite Products of Surreal Probabilities.

Python 3.10+, standard library only. This is not an infinite-theorem proof
checker, a surreal implementation, or a Lean formalization.

Run from the package root:
    python code/verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable, Mapping, Sequence

Series = dict[int, F]


class Checks:
    def __init__(self) -> None:
        self.counts: dict[str, int] = {}

    def require(self, group: str, condition: bool, detail: str) -> None:
        if not condition:
            raise AssertionError(f"{group}: {detail}")
        self.counts[group] = self.counts.get(group, 0) + 1


def clean(a: Mapping[int, F]) -> Series:
    return {e: F(c) for e, c in a.items() if c}


def add(a: Mapping[int, F], b: Mapping[int, F]) -> Series:
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, F(0)) + c
    return clean(out)


def scale(a: Mapping[int, F], c: F) -> Series:
    return clean({e: c * x for e, x in a.items()})


def mul(a: Mapping[int, F], b: Mapping[int, F]) -> Series:
    out: Series = {}
    for e, x in a.items():
        for f, y in b.items():
            out[e + f] = out.get(e + f, F(0)) + x * y
    return clean(out)


def product_series(factors: Iterable[Mapping[int, F]]) -> Series:
    out = {0: F(1)}
    for factor in factors:
        out = mul(out, factor)
    return out


def law(probs: Sequence[Mapping[int, F]]) -> dict[tuple[int, ...], Series]:
    result: dict[tuple[int, ...], Series] = {}
    for bits in itertools.product((0, 1), repeat=len(probs)):
        factors = [p if x else add({0: F(1)}, scale(p, F(-1)))
                   for p, x in zip(probs, bits)]
        result[bits] = product_series(factors)
    return result


def words(total: int, alphabet: tuple[int, ...] = (1, 2)) -> Iterable[tuple[int, ...]]:
    if total == 0:
        yield ()
    else:
        for e in alphabet:
            if e <= total:
                for tail in words(total - e, alphabet):
                    yield (e,) + tail


def q_value(vectors: Sequence[Sequence[F]], signs: Sequence[int]) -> F:
    k, n = len(vectors), len(signs)
    if k > n:
        return F(0)
    total = F(0)
    for indices in itertools.permutations(range(n), k):
        term = F(1)
        for r, j in enumerate(indices):
            term *= vectors[r][j] * signs[j]
        total += term
    return total / math.factorial(k)


def perform() -> dict[str, object]:
    checks = Checks()
    arrays = [
        [{0: F(1, 2), 1: F(j + 1, 7), 2: F((-1)**j, 11)}
         for j in range(5)],
        [{0: F(j + 1, j + 3), 1: F((-1)**j, j + 2)}
         for j in range(5)],
        [{1: F(1, (j + 1)**2), 2: F((-1)**j, j + 5)}
         for j in range(5)],
    ]
    for scenario, probs in enumerate(arrays):
        prior = {(): {0: F(1)}}
        for n in range(1, len(probs) + 1):
            current = law(probs[:n])
            total: Series = {}
            for mass in current.values():
                total = add(total, mass)
                checks.require("finite_probability_positivity",
                               mass[min(mass)] > 0,
                               f"scenario={scenario}, n={n}, mass={mass}")
            checks.require("normalization", total == {0: F(1)},
                           f"scenario={scenario}, n={n}")
            for prefix, expected in prior.items():
                observed = add(current[prefix + (0,)], current[prefix + (1,)])
                checks.require("marginal_consistency", observed == expected,
                               f"scenario={scenario}, n={n}, prefix={prefix}")
            prior = current

    # Direct likelihood vs ordered exponent words with 1/k! normalization.
    n = 4
    a = {1: [F(1, 2), F(-2, 3), F(3, 5), F(1, 7)],
         2: [F(-1, 3), F(2, 5), F(4, 7), F(-1, 11)]}
    b = {e: [2 * x for x in v] for e, v in a.items()}
    probs = [{0: F(1, 2), 1: a[1][j], 2: a[2][j]} for j in range(n)]
    masses = law(probs)
    for bits, mass in masses.items():
        signs = tuple(2*x - 1 for x in bits)
        for rho in range(1, 2*n + 1):
            expanded = sum((q_value([b[e] for e in word], signs)
                            for word in words(rho)), F(0))
            direct = 2**n * mass.get(rho, F(0))
            checks.require("ordered_word_coefficient_identity", direct == expanded,
                           f"bits={bits}, exponent={rho}")

    # Orthogonal multilinear estimate, squared to remain exact rational.
    vectors = [
        [F(1, 2), F(-2, 3), F(3, 5), F(1, 7), F(0)],
        [F(-1, 3), F(2, 5), F(4, 7), F(-1, 11), F(1, 13)],
        [F(2), F(0), F(-1, 2), F(2, 3), F(-3, 4)],
    ]
    for k in (1, 2, 3):
        for selection in itertools.product(range(3), repeat=k):
            selected = [vectors[i] for i in selection]
            norm2 = sum((q_value(selected, signs)**2
                         for signs in itertools.product((-1, 1), repeat=5)), F(0)) / 32
            bound2 = F(1, math.factorial(k))
            for v in selected:
                bound2 *= sum((c*c for c in v), F(0))
            checks.require("multilinear_L2_bound", norm2 <= bound2,
                           f"k={k}, selection={selection}")

    samples: list[dict[str, object]] = []
    for n in range(1, 9):
        interior = law([{0: F(1, 2), 1: F(1)} for _ in range(n)])
        observed = sum((abs(m.get(1, F(0))) for m in interior.values()), F(0))
        expected = 4 * sum((F(math.comb(n, k), 2**n) * abs(F(k) - F(n, 2))
                            for k in range(n+1)), F(0))
        checks.require("interior_first_order_variation", observed == expected, f"n={n}")
        checks.require("interior_moment_bounds", F(n, 3) <= (observed/2)**2 <= n,
                       f"n={n}")
        boundary = law([{1: F(1)} for _ in range(n)])
        bv = sum((abs(m.get(1, F(0))) for m in boundary.values()), F(0))
        checks.require("boundary_first_order_variation", bv == 2*n, f"n={n}")
        samples.append({"n": n, "interior_variation": str(observed),
                        "boundary_variation": str(bv)})

    # Nonidentical signed endpoint tangent identity, distinct singleton atoms.
    row = [F(1, 2), F(-2, 3), F(3, 7), F(-1, 11), F(0)]
    for n in range(1, len(row)+1):
        endpoint = law([{1: c} for c in row[:n]])
        actual = sum((abs(m.get(1, F(0))) for m in endpoint.values()), F(0))
        expected = sum((abs(c) for c in row[:n]), F(0)) + abs(sum(row[:n], F(0)))
        checks.require("signed_endpoint_tangent_variation", actual == expected, f"n={n}")

    # Finite cylinders of P0 + t(delta_y-delta_x), x=all-zero, y=all-one.
    for n in range(1, 9):
        total: Series = {}
        for bits in itertools.product((0, 1), repeat=n):
            correction = F(int(all(bits)) - int(not any(bits)))
            mass = clean({0: F(1, 2**n), 1: correction})
            checks.require("counterexample_positive_cylinders", mass[min(mass)] > 0,
                           f"n={n}, bits={bits}")
            total = add(total, mass)
        checks.require("counterexample_normalization", total == {0: F(1)}, f"n={n}")
    negative_singleton_formula = {1: F(-1)}
    checks.require("counterexample_singleton_formula",
                   negative_singleton_formula[min(negative_singleton_formula)] < 0,
                   "negative leading coefficient in the singleton formula")

    return {
        "status": "PASS",
        "arithmetic": "Exact fractions.Fraction; no floating-point comparisons",
        "assertions_passed": sum(checks.counts.values()),
        "groups": checks.counts,
        "first_order_samples": samples,
        "limitations": [
            "Finite algebraic checks only; not a proof of any infinite extension theorem.",
            "Integer-exponent test representation does not implement arbitrary-rank Hahn fields.",
            "Atomlessness and all-event positivity are established in the article, not by enumeration.",
            "No Lean formalization or independent proof certification is supplied.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    result = perform()
    text = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
