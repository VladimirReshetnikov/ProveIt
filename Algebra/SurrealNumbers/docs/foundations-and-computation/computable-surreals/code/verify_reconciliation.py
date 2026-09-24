#!/usr/bin/env python3
"""Cross-model finite checks for the reconciled report (Python 3.10+).

Standard-library exact rational arithmetic only. The test fixtures are finite;
this program is not an implementation of arbitrary computable reals or infinite
surreal names, a halting oracle, or a proof of the report's infinite theorems.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as Q
from math import ceil, lcm
from pathlib import Path
from random import Random
from typing import Callable

Series = dict[Q, Q]
COUNTS: Counter[str] = Counter()


def check(group: str, condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {description}")
    COUNTS[group] += 1


def clean(x: Series) -> Series:
    return {Q(q): Q(a) for q, a in x.items() if a}


def add(x: Series, y: Series) -> Series:
    z = dict(x)
    for q, a in y.items():
        z[q] = z.get(q, Q(0)) + a
    return clean(z)


def scale(x: Series, a: Q) -> Series:
    return clean({q: a*b for q, b in x.items()})


def multiply(x: Series, y: Series) -> Series:
    z: Series = {}
    for q, a in x.items():
        for r, b in y.items():
            z[q+r] = z.get(q+r, Q(0)) + a*b
    return clean(z)


def derivative(x: Series) -> Series:
    return clean({q-1: q*a for q, a in x.items()})


def primitive_zero_constant(x: Series) -> Series:
    return clean({q+1: a/(q+1) for q, a in x.items() if q != -1})


@dataclass(frozen=True)
class FiniteName:
    """A finite test instance of the report's redundant candidate-cover API."""
    coefficients: Series
    lower_bound: Q

    def coefficient(self, q: Q) -> Q:
        return self.coefficients.get(q, Q(0))

    def cover(self, bound: Q) -> set[Q]:
        # Real support is always included. Extra candidates intentionally change
        # with the cutoff; valid covers need not be nested or omit zero entries.
        result = {q for q in self.coefficients if q < bound}
        for extra in (self.lower_bound, bound-Q(1, 7)):
            if self.lower_bound <= extra < bound:
                result.add(extra)
        return result


def covered_product_coefficient(x: FiniteName, y: FiniteName, q: Q) -> Q:
    return sum((x.coefficient(r)*y.coefficient(q-r)
                for r in x.cover(q-y.lower_bound+1)), Q(0))


def product_cover(x: FiniteName, y: FiniteName, bound: Q) -> set[Q]:
    lower = x.lower_bound+y.lower_bound
    return {r+s for r in x.cover(bound-y.lower_bound)
            for s in y.cover(bound-x.lower_bound) if lower <= r+s < bound}


def geometric_cover(h: FiniteName, delta: Q, bound: Q) -> set[Q]:
    """Finite model of lem:geom, retaining raw power-name zero candidates."""
    candidates: set[Q] = set()
    power: Series = {Q(0): Q(1)}
    for n in range(max(0, ceil(bound/delta))):
        # A raw multiplication name has lower bound n*lower_bound, even when
        # the actual support starts at n*delta; no zero oracle normalizes it.
        candidates.update(FiniteName(power, n*h.lower_bound).cover(bound))
        power = multiply(power, h.coefficients)
    return {q for q in candidates if 0 <= q < bound}


def test_geometric_cover_contract() -> None:
    fixtures = [
        FiniteName({}, Q(-1)),
        FiniteName({Q(1, 3): Q(2), Q(5, 3): Q(-1, 2)}, Q(-2)),
        FiniteName({Q(2): Q(1), Q(7, 3): Q(-1)}, Q(-3)),
    ]
    for case, h in enumerate(fixtures):
        delta = min({Q(1)} | {q for q in h.cover(Q(1)) if q > 0})
        # Independently form a generous exact partial sum. For all cutoffs
        # below, 33*delta > 8, so later powers cannot contribute.
        expected: Series = {}
        power: Series = {Q(0): Q(1)}
        for _ in range(33):
            expected = add(expected, power)
            power = multiply(power, h.coefficients)
        check("geometric_negative_zero_candidates",
              h.lower_bound < 0 and h.lower_bound in h.cover(Q(2))
              and h.coefficient(h.lower_bound) == 0,
              f"raw first-power cover would violate output lower bound, case {case}")
        for bound in [Q(-1), Q(0), Q(1, 7), Q(1), Q(2), Q(5, 2), Q(8)]:
            cover = geometric_cover(h, delta, bound)
            check("geometric_cover_ranges", all(0 <= q < bound for q in cover),
                  f"case {case}, cutoff {bound}")
            check("geometric_cover_completeness",
                  {q for q in expected if q < bound} <= cover,
                  f"case {case}, cutoff {bound}")


def dense_common_grid_product(d1: int, n1: int, a: list[Q],
                              d2: int, n2: int, b: list[Q]) -> Series:
    """Independent common-denominator dense convolution, including zero slots."""
    d = lcm(d1, d2)
    start_a, start_b = n1*(d//d1), n2*(d//d2)
    aa = [Q(0)] * ((len(a)-1)*(d//d1)+1)
    bb = [Q(0)] * ((len(b)-1)*(d//d2)+1)
    for i, value in enumerate(a):
        aa[i*(d//d1)] = value
    for i, value in enumerate(b):
        bb[i*(d//d2)] = value
    cc = [sum((aa[j]*bb[i-j] for j in range(len(aa))
               if 0 <= i-j < len(bb)), Q(0))
          for i in range(len(aa)+len(bb)-1)]
    return clean({Q(start_a+start_b+i, d): value
                  for i, value in enumerate(cc)})


def test_models(rng: Random) -> None:
    for case in range(64):
        d1, d2 = rng.randint(1, 6), rng.randint(1, 6)
        n1, n2 = rng.randint(-6, 3), rng.randint(-6, 3)
        a = [Q(rng.randint(-4, 4), rng.randint(1, 7))
             for _ in range(rng.randint(2, 10))]
        b = [Q(rng.randint(-4, 4), rng.randint(1, 7))
             for _ in range(rng.randint(2, 10))]
        xx = clean({Q(n1+i, d1): value for i, value in enumerate(a)})
        yy = clean({Q(n2+i, d2): value for i, value in enumerate(b)})
        x, y = FiniteName(xx, Q(n1, d1)), FiniteName(yy, Q(n2, d2))
        product = multiply(xx, yy)
        dense = dense_common_grid_product(d1, n1, a, d2, n2, b)
        check("dense_sparse_convolution", product == dense, f"case {case}")
        targets = sorted(set(product) | {Q(j, 3) for j in range(-12, 13)})
        for q in targets:
            check("covered_coefficients",
                  covered_product_coefficient(x, y, q) == product.get(q, Q(0)),
                  f"case {case}, target {q}")
        for bound in [Q(-3), Q(0), Q(1, 3), Q(1), Q(7, 2), Q(8)]:
            cover = product_cover(x, y, bound)
            check("finite_cover_completeness",
                  {q for q in product if q < bound} <= cover,
                  f"case {case}, cutoff {bound}")
            check("finite_cover_ranges",
                  all(x.lower_bound+y.lower_bound <= q < bound for q in cover),
                  f"case {case}, cutoff {bound}")
    zero = FiniteName({}, Q(0))
    check("redundant_nonnested_covers", Q(6, 7) in zero.cover(Q(1)),
          "first cutoff contains a zero candidate")
    check("redundant_nonnested_covers", Q(6, 7) not in zero.cover(Q(2)),
          "that candidate need not persist at a larger cutoff")
    check("redundant_nonnested_covers", zero.cover(Q(-1)) == set(),
          "cutoff below lower bound")


def test_residues(rng: Random) -> None:
    for case in range(80):
        x = clean({Q(j, 3): Q(rng.randint(-5, 5), rng.randint(1, 9))
                   for j in range(-9, 10)})
        x0 = {Q(0): x.get(Q(0), Q(0))}
        residue_term = {Q(-1): x.get(Q(-1), Q(0))}
        check("primitive_derivative_identity",
              primitive_zero_constant(derivative(x)) == add(x, scale(x0, Q(-1))),
              f"I0(Dx)=x-a0, case {case}")
        check("derivative_primitive_identity",
              derivative(primitive_zero_constant(x)) == add(x, scale(residue_term, Q(-1))),
              f"D(I0x)=x-res(x)t^-1, case {case}")
        check("derivative_residue_zero", derivative(x).get(Q(-1), Q(0)) == 0,
              f"case {case}")
        check("leibniz_rule",
              derivative(multiply(x, x)) == scale(multiply(x, derivative(x)), Q(2)),
              f"case {case}")


def test_finite_jet() -> None:
    # Formal bivariate coefficient keys are (u exponent, Z degree).
    y = {(1, 0): Q(1), (2, 1): Q(1)}
    square: dict[tuple[int, int], Q] = {}
    for (q, j), a in y.items():
        for (r, k), b in y.items():
            key = (q+r, j+k)
            square[key] = square.get(key, Q(0)) + a*b
    square[(2, 0)] = square.get((2, 0), Q(0))-1
    square[(3, 0)] = square.get((3, 0), Q(0))-1
    transformed = {(q-3, j): a for (q, j), a in square.items() if a}
    check("finite_jet_transform", transformed == {(0, 0): Q(-1),
          (0, 1): Q(2), (1, 2): Q(1)}, "u^-3 f(u+u^2Z)=-1+2Z+uZ^2")
    count = 22
    z = [Q(1, 2)]
    for n in range(1, count):
        z.append(-sum((z[j]*z[n-1-j] for j in range(n)), Q(0))/2)
    yy = {Q(1): Q(1)} | {Q(n+2): a for n, a in enumerate(z)}
    residual = add(multiply(yy, yy), {Q(2): Q(-1), Q(3): Q(-1)})
    for q in range(count+3):
        check("finite_jet_root_coefficients", residual.get(Q(q), Q(0)) == 0,
              f"root equation coefficient {q}")
    binomial = Q(1)
    for n in range(count+1):
        check("finite_jet_binomial_agreement", yy.get(Q(n+1), Q(0)) == binomial,
              f"coefficient u^{n+1}")
        binomial *= (Q(1, 2)-n)/(n+1)


def test_unbounded_denominators() -> None:
    aa = [Q(n)+Q(1, n+1) for n in range(1, 97)]
    cc = [Q(n)+Q(1, 2**n) for n in range(1, 97)]
    for label, sequence, denominator in (
            ("A", aa, lambda n: n+1), ("C", cc, lambda n: 2**n)):
        for n, q in enumerate(sequence, start=1):
            check("denominator_fixtures", q.denominator == denominator(n),
                  f"{label}, n={n}")
            check("left_finite_cutoff_fixtures", n < q < n+1,
                  f"{label}, n={n}")
        check("support_strict_increase", all(x < y for x, y in zip(sequence, sequence[1:])),
              label)
        for bound in [Q(0), Q(1), Q(3, 2), Q(13, 3), Q(96)]:
            candidates = {sequence[n-1] for n in range(1, min(96, max(0, ceil(bound)))+1)}
            candidates = {q for q in candidates if q < bound}
            check("left_finite_cutoff_fixtures", {q for q in sequence if q < bound} == candidates,
                  f"{label}, bound={bound}")


def run() -> dict[str, object]:
    COUNTS.clear()
    seed = 20260921
    rng = Random(seed)
    test_models(rng)
    test_geometric_cover_contract()
    test_residues(rng)
    test_finite_jet()
    test_unbounded_denominators()
    return {"status": "PASS", "seed": seed, "total_checks": sum(COUNTS.values()),
            "groups": dict(sorted(COUNTS.items())),
            "scope": "Finite exact-rational fixtures only, not proof of infinite theorems."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON result path")
    args = parser.parse_args()
    text = json.dumps(run(), indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
