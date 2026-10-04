#!/usr/bin/env python3
"""Exact finite checks for One Real Dimension, Arbitrarily Complicated Arithmetic.

These deterministic checks exercise finite rational shadows of the formulas.
They are NOT a formal proof of the infinite, topological, or descriptive-set-
theoretic theorems. No third-party packages or floating-point calculations.
Run: python3 checks/verify_finite.py --output checks/results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
from typing import Iterable, Sequence

SEED = 20261004
COUNTS: Counter[str] = Counter()
RNG = random.Random(SEED)


def check(condition: bool, family: str, detail: object = None) -> None:
    """Use an explicit exception so checks also execute with python -O."""
    if not condition:
        raise AssertionError(f"{family}: {detail!r}")
    COUNTS[family] += 1


def sign(q: Q | int) -> int:
    return (q > 0) - (q < 0)


def lex_sign(values: Iterable[Q | int]) -> int:
    for q in values:
        if q:
            return sign(q)
    return 0


@dataclass(frozen=True)
class Element:
    real: Q
    vector: tuple[Q, ...]
    integer: int

    def __add__(self, other: Element) -> Element:
        if len(self.vector) != len(other.vector):
            raise ValueError("Dimension mismatch")
        return Element(self.real + other.real,
                       tuple(a + b for a, b in zip(self.vector, other.vector)),
                       self.integer + other.integer)

    def __neg__(self) -> Element:
        return Element(-self.real, tuple(-x for x in self.vector), -self.integer)

    def __sub__(self, other: Element) -> Element:
        return self + (-other)

    def scale(self, n: int) -> Element:
        return Element(n * self.real, tuple(n * x for x in self.vector),
                       n * self.integer)


def zero(d: int) -> Element:
    return Element(Q(0), (Q(0),) * d, 0)


def unit(d: int) -> Element:
    return Element(Q(0), (Q(0),) * d, 1)


def sample(d: int) -> Element:
    rational = lambda: Q(RNG.randint(-8, 8), RNG.randint(1, 6))
    return Element(rational(), tuple(rational() for _ in range(d)),
                   RNG.randint(-20, 20))


def normal_sign(x: Element, order: Sequence[int], real_position: int) -> int:
    """Earlier coordinates dominate; the integer is always last."""
    if sorted(order) != list(range(len(x.vector))):
        raise ValueError("order must permute the coordinate indices")
    if not 0 <= real_position <= len(order):
        raise ValueError("Invalid real position")
    values = [x.vector[i] for i in order]
    values.insert(real_position, x.real)
    values.append(Q(x.integer))
    return lex_sign(values)


def shear(x: Element, weights: Sequence[Q]) -> Element:
    if len(weights) != len(x.vector):
        raise ValueError("Dimension mismatch")
    return Element(x.real + sum((a*b for a, b in zip(weights, x.vector)), Q(0)),
                   x.vector, x.integer)


def independent_cut_sign(x: Element, order: Sequence[int], p: int,
                         weights: Sequence[Q]) -> int:
    """Sign by outer quotient, relative real cut, then infinitesimals."""
    outer = lex_sign(x.vector[i] for i in order[:p])
    if outer:
        return outer
    cut = x.real + sum((a*b for a, b in zip(weights, x.vector)), Q(0))
    if cut:
        return sign(cut)
    return lex_sign([*(x.vector[i] for i in order[p:]), x.integer])


def quotient_remainder(x: Element, n: int) -> tuple[Element, int]:
    if n < 1:
        raise ValueError("Positive modulus required")
    zq, r = divmod(x.integer, n)
    return Element(x.real/n, tuple(v/n for v in x.vector), zq), r


def permutation_transport(x: Element, perm: Sequence[int]) -> Element:
    out = [Q(0)] * len(x.vector)
    for old, new in enumerate(perm):
        out[new] = x.vector[old]
    return Element(x.real, tuple(out), x.integer)


def check_coordinate_orders() -> None:
    # All 3! orders and all four placements of the real coordinate.
    for order in itertools.permutations(range(3)):
        for p in range(4):
            check(normal_sign(unit(3), order, p) == 1, "unit_positive")
            for _ in range(250):
                x, y, t = sample(3), sample(3), sample(3)
                sx, sy = normal_sign(x, order, p), normal_sign(y, order, p)
                check(normal_sign(-x, order, p) == -sx, "sign_negation")
                check((sx == 0) == (x == zero(3)), "sign_separation")
                check(normal_sign((x+t)-(y+t), order, p) ==
                      normal_sign(x-y, order, p), "translation_invariance")
                if sx > 0 and sy > 0:
                    check(normal_sign(x+y, order, p) > 0, "positive_cone_addition")
                if sx > 0:
                    check(normal_sign(x-unit(3), order, p) >= 0,
                          "least_positive_unit")
                for n in (1, 2, 3, 5, 11):
                    q, r = quotient_remainder(x, n)
                    check(q.scale(n)+unit(3).scale(r) == x, "residue_identity")
                    check(0 <= r < n, "residue_range")
                    if sx >= 0:
                        check(normal_sign(q, order, p) >= 0,
                              "positive_quotient")
    # Explicit boundary and negative-constant cases, not just random samples.
    for p in range(4):
        order = (0, 1, 2)
        for z in range(-31, 32):
            for r in (Q(0), Q(1, 7), Q(-1, 7)):
                x = Element(r, (Q(0),)*3, z)
                for n in range(1, 13):
                    q, rem = quotient_remainder(x, n)
                    check(q.scale(n)+unit(3).scale(rem) == x,
                          "boundary_negative_constant_division")


def check_shears() -> None:
    offsets = (Q(-2), Q(0), Q(1, 2))
    for order in itertools.permutations(range(3)):
        for p in range(4):
            for weights in itertools.product(offsets, repeat=3):
                neg_weights = tuple(-w for w in weights)
                for _ in range(12):
                    x, y = sample(3), sample(3)
                    # Force samples onto the tilted boundary as well.
                    boundary = Element(-sum((w*v for w, v in
                                             zip(weights, x.vector)), Q(0)),
                                       x.vector, x.integer)
                    for point in (x, boundary):
                        check(independent_cut_sign(point, order, p, weights) ==
                              normal_sign(shear(point, weights), order, p),
                              "normal_form_cut_sign")
                        check(shear(shear(point, weights), neg_weights) == point,
                              "shear_inverse")
                    check(shear(x+y, weights) == shear(x, weights)+shear(y, weights),
                          "shear_addition")
                check(shear(unit(3), weights) == unit(3), "shear_unit")


def check_permutations_and_spines() -> None:
    for d in range(1, 6):
        for _ in range(500):
            order = list(range(d)); RNG.shuffle(order)
            perm = list(range(d)); RNG.shuffle(perm)
            new_order = [perm[i] for i in order]
            x, y = sample(d), sample(d)
            p = RNG.randrange(d+1)
            check(normal_sign(x, order, p) ==
                  normal_sign(permutation_transport(x, perm), new_order, p),
                  "permutation_sign")
            check(permutation_transport(x+y, perm) ==
                  permutation_transport(x, perm)+permutation_transport(y, perm),
                  "permutation_addition")
            i = RNG.randrange(d)
            vx = [Q(0)]*d; vy = [Q(0)]*d
            lead = order[i]
            vx[lead] = Q(RNG.randint(1, 9), RNG.randint(1, 9))
            vy[lead] = Q(RNG.randint(1, 9), RNG.randint(1, 9))
            for j in order[i+1:]:
                vx[j] = Q(RNG.randint(-9, 9), RNG.randint(1, 9))
                vy[j] = Q(RNG.randint(-9, 9), RNG.randint(1, 9))
            n = int(vx[lead] / vy[lead]) + 1
            m = int(vy[lead] / vx[lead]) + 1
            check(lex_sign(n*vy[j]-vx[j] for j in order) > 0,
                  "archimedean_witness_forward")
            check(lex_sign(m*vx[j]-vy[j] for j in order) > 0,
                  "archimedean_witness_reverse")
            if i+1 < d:
                late = [Q(0)]*d; late[order[i+1]] = Q(7, 3)
                for k in (1, 2, 100, 10000):
                    check(lex_sign(vx[j]-k*late[j] for j in order) > 0,
                          "different_leading_scale_sampled_dominance")


def check_fixed_carrier() -> None:
    # Finite coordinate labels, with exact positive real BEFORE log chart.
    # H is represented here by rational vectors and integer constants.
    for order in itertools.permutations(range(3)):
        labels = list(itertools.product((-1, 0, 1), repeat=4))
        def hsign(label: tuple[int, ...]) -> int:
            return lex_sign([*(label[i] for i in order), label[-1]])
        def element(label: tuple[int, ...], real: Q) -> Element:
            return Element(real, tuple(Q(q) for q in label[:-1]), label[-1])
        for label in labels:
            # Closed-half-line versus open-line chart classification.
            kind = "closed" if hsign(label) >= 0 else "open"
            for real in (Q(0), Q(1, 9), Q(5, 2)):
                admissible = kind == "closed" or real > 0
                check(admissible == (normal_sign(element(label, real), order, 0) >= 0),
                      "carrier_fiber_membership")
        for _ in range(1200):
            h, k = RNG.choice(labels), RNG.choice(labels)
            r = RNG.choice((Q(0), Q(1, 9), Q(5, 2)))
            s = RNG.choice((Q(0), Q(2, 7), Q(3, 2)))
            if hsign(h) < 0 and r == 0:
                r = Q(1, 9)
            if hsign(k) < 0 and s == 0:
                s = Q(2, 7)
            x, y = element(h, r), element(k, s)
            out = x+y
            out_label = tuple(a+b for a, b in zip(h, k))
            check(out == element(out_label, r+s), "carrier_transport_addition")
            check(normal_sign(out, order, 0) >= 0, "carrier_output_positive")
            if hsign(out_label) < 0:
                check(out.real > 0, "log_chart_never_receives_zero")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    check_coordinate_orders()
    check_shears()
    check_permutations_and_spines()
    check_fixed_carrier()
    result = {
        "status": "PASS", "seed": SEED, "arithmetic": "exact fractions.Fraction",
        "third_party_dependencies": [], "total_checks": sum(COUNTS.values()),
        "counts": dict(sorted(COUNTS.items())),
        "scope": {
            "coordinate_models": "all 3! coordinate orders times 4 real positions",
            "offset_vectors": "27 rational vectors for each coordinate model",
            "permutation_dimensions": [1, 2, 3, 4, 5],
            "carrier_chart": "positive real coordinate before logarithmic recharting",
        },
        "limitations": [
            "Finite rational samples do not prove statements about all orders or reals.",
            "Sampled dominance at four multipliers is not a proof of infinite dominance.",
            "No infinite isomorphism, Borel-completeness, topology, or Hamel-basis test.",
            "This is not a Lean/Rocq kernel certificate."
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
