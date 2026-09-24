#!/usr/bin/env python3
"""Exact finite checks accompanying `omnific_set_shadows.tex`.

This program does NOT implement full Hahn fields, surreal cuts, transfinite
supports, cardinal arithmetic, maximal-ideal existence, or formal proofs.
It checks finite algebraic identities over Q and finite rings. No third-party
packages or network access are required. Python 3.10 or later is sufficient.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import gcd
from pathlib import Path
import random
from typing import Iterable, Mapping, TypeAlias

Exponent: TypeAlias = tuple[Fraction, Fraction, Fraction]
Polynomial: TypeAlias = dict[Exponent, Fraction]
ZERO: Exponent = (Fraction(0), Fraction(0), Fraction(0))


def exponent(*values: int | Fraction) -> Exponent:
    if len(values) != 3:
        raise ValueError("An exponent must have exactly three coordinates.")
    if any(not isinstance(v, (int, Fraction)) for v in values):
        raise TypeError("Exponent coordinates must be integers or Fractions.")
    return (Fraction(values[0]), Fraction(values[1]), Fraction(values[2]))


def eadd(a: Exponent, b: Exponent) -> Exponent:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def escale(n: int | Fraction, a: Exponent) -> Exponent:
    return tuple(Fraction(n) * x for x in a)  # type: ignore[return-value]


def polynomial(terms: Iterable[tuple[Exponent, int | Fraction]]) -> Polynomial:
    out: Polynomial = {}
    for e, c in terms:
        out[e] = out.get(e, Fraction(0)) + Fraction(c)
    return {e: c for e, c in out.items() if c != 0}


def mono(e: Exponent, c: int | Fraction = 1) -> Polynomial:
    return polynomial([(e, c)])


def add(*polys: Mapping[Exponent, Fraction]) -> Polynomial:
    return polynomial((e, c) for p in polys for e, c in p.items())


def scale(c: int | Fraction, p: Mapping[Exponent, Fraction]) -> Polynomial:
    return polynomial((e, Fraction(c) * a) for e, a in p.items())


def shift(p: Mapping[Exponent, Fraction], delta: Exponent) -> Polynomial:
    return polynomial((eadd(e, delta), c) for e, c in p.items())


def mul(p: Mapping[Exponent, Fraction], q: Mapping[Exponent, Fraction]) -> Polynomial:
    return polynomial((eadd(e, f), c * d)
                      for e, c in p.items() for f, d in q.items())


def ct(p: Mapping[Exponent, Fraction]) -> Fraction:
    return p.get(ZERO, Fraction(0))


def eval_one(p: Mapping[Exponent, Fraction]) -> Fraction:
    return sum(p.values(), Fraction(0))


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def check(self, family: str, condition: bool, detail: str) -> None:
        if not condition:
            raise AssertionError(f"{family}: {detail}")
        self.counts[family] += 1


def run_checks() -> dict[str, object]:
    checks = Checks()
    one = mono(ZERO)
    gamma = exponent(1, 0, 0)
    pairs = [
        (exponent(0, 3, 0), exponent(0, 1, 0)),
        (exponent(0, 0, 3), exponent(0, 0, 1)),
        (exponent(0, 1, 0), exponent(0, 0, 2)),
        (exponent(0, 2, -7), exponent(0, 1, 9)),
        (exponent(0, Fraction(1, 2), 3),
         exponent(0, Fraction(1, 3), -2)),
    ]
    f = polynomial([
        (exponent(2, -1, 0), 3),
        (exponent(1, 2, 0), -2),
        (exponent(1, -1, 3), Fraction(5, 7)),
    ])
    for pair_id, (a, b) in enumerate(pairs):
        checks.check("parameter_order", a > b > ZERO,
                     f"pair {pair_id} must satisfy a>b>0")
        delta = eadd(a, escale(-1, b))
        factor = add(mono(a), mono(b, -1))
        for n in range(13):
            q = polynomial((eadd(gamma, eadd(escale(-1, a), escale(-j, delta))), 1)
                           for j in range(n + 1))
            rem_exp = eadd(gamma, escale(-(n + 1), delta))
            expected = add(mono(gamma), mono(rem_exp, -1))
            checks.check("geometric_truncation", mul(factor, q) == expected,
                         f"pair={pair_id}, N={n}")
            checks.check("positive_exponents", all(e > ZERO for e in q) and rem_exp > ZERO,
                         f"pair={pair_id}, N={n}")
            qf = add(*(shift(f, eadd(escale(-1, a), escale(-j, delta)))
                       for j in range(n + 1)))
            expected_f = add(f, scale(-1, shift(f, escale(-(n + 1), delta))))
            checks.check("polynomial_geometric_truncation",
                         mul(factor, qf) == expected_f,
                         f"pair={pair_id}, N={n}")

        # (1-X^a)(-sum_{j=1}^N X^(gamma-ja)) = X^gamma-X^(gamma-Na).
        for n in range(1, 13):
            qn = polynomial((eadd(gamma, escale(-j, a)), -1)
                            for j in range(1, n + 1))
            lhs = add(add(one, mono(gamma, -1)),
                      mul(add(one, mono(a, -1)), qn),
                      mono(eadd(gamma, escale(-n, a))))
            checks.check("comaximal_truncation", lhs == one,
                         f"pair={pair_id}, N={n}")

    rng = random.Random(20260922)
    pool = [ZERO, exponent(0, 0, 1), exponent(0, 1, -2),
            exponent(1, -5, 3), exponent(0, Fraction(1, 2), 4),
            exponent(2, 0, 0), exponent(0, 0, Fraction(3, 2))]
    for trial in range(80):
        def sample_poly() -> Polynomial:
            return polynomial((e, rng.randint(-5, 5) if e == ZERO else
                               Fraction(rng.randint(-5, 5), rng.randint(1, 5)))
                              for e in pool)
        p, q = sample_poly(), sample_poly()
        pq = mul(p, q)
        checks.check("constant_multiplicativity", ct(pq) == ct(p) * ct(q),
                     f"trial={trial}")
        checks.check("finite_support_evaluation", eval_one(pq) == eval_one(p) * eval_one(q),
                     f"trial={trial}")

    # Gaussian constants modulo 2, with i acting as 1 on M=F_2.
    # delta(a+bi)=b; action(a+bi)=a+b; (a+bi)(c+di)=(ac-bd)+(ad+bc)i.
    for a, b, c, d in product(range(2), repeat=4):
        delta_xy = (a * d + b * c) % 2
        leibniz = ((a + b) * d + (c + d) * b) % 2
        checks.check("gaussian_derivation_mod2", delta_xy == leibniz,
                     f"x=({a},{b}), y=({c},{d})")
    checks.check("gaussian_nonzero_derivation", 1 % 2 != 0,
                 "delta(i)=1 in F_2")
    for p in [3, 5, 7, 11]:
        # In Z[i]/p, the formal element 2i is nonzero; delta(i)=1 is forbidden.
        checks.check("odd_characteristic_obstruction", (0, 2 % p) != (0, 0),
                     f"2i must remain nonzero modulo {p}")

    for d in range(13):
        for n in range(1, 13):
            actual = {(d * r) % n for r in range(n)}
            expected = {r for r in range(n) if r % gcd(d, n) == 0}
            checks.check("gcd_congruence_ideals", actual == expected,
                         f"d={d}, n={n}")

    return {
        "status": "PASS",
        "arithmetic": "Exact fractions over Q and explicitly finite residue rings",
        "random_seed": 20260922,
        "assertions_total": sum(checks.counts.values()),
        "assertions_by_family": dict(sorted(checks.counts.items())),
        "not_verified": [
            "Hahn summability or arbitrary infinite supports",
            "Existence of surreal cuts and full-class statements",
            "Infinite cardinal arithmetic and sharp cardinal thresholds",
            "Maximal-ideal existence or residue-field classifications",
            "Proof-assistant verification or historical novelty",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification.json"),
                        help="Destination for the JSON verification report")
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
