#!/usr/bin/env python3
"""Exact finite checks accompanying Three Duals at Surreal Scales.

Only the Python standard library is required (Python 3.10 or newer).
All arithmetic is rational. These finite checks do not verify well-ordering
of infinite supports, Hahn--Banach, Hamel choices, or invisible functionals.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
from random import Random
from typing import Callable, TypeVar

Exp = tuple[Q, Q]  # Lexicographically ordered rational pairs.
Vec = tuple[Q, ...]
Mat = tuple[Vec, ...]
T = TypeVar("T")
U = TypeVar("U")
R = TypeVar("R")
ZERO: Exp = (Q(0), Q(0))


def exp(a: int | Q, b: int | Q) -> Exp:
    return (Q(a), Q(b))


def eadd(a: Exp, b: Exp) -> Exp:
    return (a[0] + b[0], a[1] + b[1])


def vadd(a: Vec, b: Vec) -> Vec:
    if len(a) != len(b):
        raise ValueError("Vector dimensions do not match")
    return tuple(x + y for x, y in zip(a, b))


def vscale(a: Q, v: Vec) -> Vec:
    return tuple(a * x for x in v)


def madd(a: Mat, b: Mat) -> Mat:
    if len(a) != len(b):
        raise ValueError("Matrix row counts do not match")
    return tuple(vadd(x, y) for x, y in zip(a, b))


def mvec(a: Mat, b: Vec) -> Vec:
    if any(len(row) != len(b) for row in a):
        raise ValueError("Matrix-vector dimensions do not match")
    return tuple(sum((x * y for x, y in zip(row, b)), Q(0)) for row in a)


def mmul(a: Mat, b: Mat) -> Mat:
    if not b or any(len(row) != len(b) for row in a):
        raise ValueError("Matrix product dimensions do not match")
    columns = tuple(zip(*b))
    return tuple(tuple(sum((x * y for x, y in zip(row, col)), Q(0))
                       for col in columns) for row in a)


def dot(a: Vec, b: Vec) -> Q:
    if len(a) != len(b):
        raise ValueError("Inner-product dimensions do not match")
    return sum((x * y for x, y in zip(a, b)), Q(0))


def nonzero(x: object) -> bool:
    if isinstance(x, tuple):
        return any(nonzero(y) for y in x)
    return x != 0


def convolution(a: dict[Exp, T], b: dict[Exp, U],
                product: Callable[[T, U], R],
                addition: Callable[[R, R], R]) -> dict[Exp, R]:
    """Finite convolution, retaining cancellation and omitting zero outputs."""
    out: dict[Exp, R] = {}
    for alpha, u in a.items():
        for beta, w in b.items():
            eta = eadd(alpha, beta)
            term = product(u, w)
            out[eta] = addition(out[eta], term) if eta in out else term
    return {eta: value for eta, value in out.items() if nonzero(value)}


def series_sum(series: list[dict[Exp, Vec]]) -> dict[Exp, Vec]:
    out: dict[Exp, Vec] = {}
    for s in series:
        for eta, v in s.items():
            out[eta] = vadd(out[eta], v) if eta in out else v
    return {eta: v for eta, v in out.items() if nonzero(v)}


def coefficient_rank(vectors: list[Vec]) -> int:
    """Exact Gaussian elimination; vectors are treated as matrix rows."""
    if not vectors:
        return 0
    width = len(vectors[0])
    if any(len(v) != width for v in vectors):
        raise ValueError("Rank inputs have inconsistent dimensions")
    a = [list(row) for row in vectors]
    row = 0
    for col in range(width):
        pivot = next((r for r in range(row, len(a)) if a[r][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        scale = a[row][col]
        a[row] = [x / scale for x in a[row]]
        for r in range(row + 1, len(a)):
            factor = a[r][col]
            if factor:
                a[r] = [x - factor * y for x, y in zip(a[r], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def rank_below(s: dict[Exp, Vec], cut: Exp) -> int:
    return coefficient_rank([v for eta, v in s.items() if eta < cut])


def unit(n: int, j: int) -> Vec:
    return tuple(Q(i == j) for i in range(n))


def random_vec(rng: Random, n: int) -> Vec:
    return tuple(Q(rng.randint(-4, 4), rng.randint(1, 4)) for _ in range(n))


def random_mat(rng: Random, rows: int, cols: int) -> Mat:
    return tuple(random_vec(rng, cols) for _ in range(rows))


def run_checks() -> dict[str, object]:
    rng = Random(20260922)
    counts: dict[str, int] = defaultdict(int)

    def check(group: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(f"Failed exact check in {group}")
        counts[group] += 1

    supports = [exp(0, 0), exp(0, 1), exp(0, 2), exp(1, 0)]
    for _ in range(60):
        a = {e: random_mat(rng, 2, 3) for e in rng.sample(supports, 3)}
        b = {e: random_mat(rng, 4, 2) for e in rng.sample(supports, 2)}
        x = {e: random_vec(rng, 3) for e in rng.sample(supports, 3)}
        ax = convolution(a, x, mvec, vadd)
        bax = convolution(b, ax, mvec, vadd)
        ba = convolution(b, a, mmul, madd)
        check("operator_composition", bax == convolution(ba, x, mvec, vadd))

        scalar = {exp(-1, 0): Q(2, 3), exp(0, 1): Q(-4, 5)}
        sx = convolution(scalar, x, vscale, vadd)
        check("scalar_compatibility",
              convolution(a, sx, mvec, vadd) ==
              convolution(scalar, ax, vscale, vadd))

        pieces = [{eta: value} for eta, value in x.items()]
        check("finite_family_regrouping", ax == series_sum(
            [convolution(a, piece, mvec, vadd) for piece in pieces]))

        sq = convolution(x, x, dot, lambda p, q: p + q)
        clean_x = {eta: value for eta, value in x.items() if nonzero(value)}
        if clean_x:
            first = min(clean_x)
            check("leading_squared_norm", min(sq) == eadd(first, first))
            check("leading_squared_norm", sq[min(sq)] == dot(clean_x[first], clean_x[first]))
            check("leading_squared_norm", sq[min(sq)] > 0)

    for n in range(2, 25):
        # Finite prefixes of the bounded increasing support 1 - 1/m.
        bounded = {exp(0, 1-Q(1, j+2)): unit(n, j) for j in range(n)}
        check("coefficient_rank_cuts", rank_below(bounded, exp(0, 1)) == n)
        check("coefficient_rank_cuts", rank_below(bounded, exp(0, Q(3, 4))) == 2)
        dependent = {eta: vscale(Q(j+1), unit(n, 0))
                     for j, eta in enumerate(bounded)}
        check("coefficient_rank_cuts", rank_below(dependent, exp(0, 1)) == 1)

        # The same support n is locally finite in Q, but all lies below (1,0).
        two_scale = {exp(0, j+1): unit(n, j) for j in range(n)}
        check("two_scale_rank", rank_below(two_scale, exp(0, 5)) == min(n, 4))
        check("two_scale_rank", rank_below(two_scale, exp(1, 0)) == n)
        check("two_scale_rank", all(eta < exp(1, 0) for eta in two_scale))

        # Finite projection algebra only; no finite-dimensional analogue
        # is claimed for the infinite theorem's zero orthogonal complement.
        phi = tuple(Q(j+1) for j in range(n))
        u = unit(n, 0)  # phi(u)=1
        p = tuple(tuple(Q(i == j) - u[i] * phi[j] for j in range(n))
                  for i in range(n))
        check("projection_algebra", mmul(p, p) == p)
        check("projection_algebra", not any(mvec((phi,), mvec(p, random_vec(rng, n)))))
        check("projection_algebra", coefficient_rank(list(p)) == n-1)

    # The first N images of the nonsummable image family all equal 1.
    # The conclusion about infinitely many contributors is in the proof.
    deltas = [Q(1, n) for n in range(1, 41)]
    check("descending_support_prefix", all(a > b for a, b in zip(deltas, deltas[1:])))
    inputs = [exp(0, -d) for d in deltas]
    check("descending_support_prefix", all(a < b for a, b in zip(inputs, inputs[1:])))
    for delta, inp in zip(deltas, inputs):
        image = convolution({inp: Q(1)}, {exp(0, delta): Q(1)},
                            lambda a, b: a*b, lambda a, b: a+b)
        check("descending_support_prefix", image == {ZERO: Q(1)})

    # Nontrivial coefficient collision and cancellation.
    cancellation = convolution({ZERO: Q(1), exp(0, 1): Q(1)},
                               {ZERO: Q(1), exp(0, 1): Q(-1)},
                               lambda a, b: a*b, lambda a, b: a+b)
    check("cancellation", cancellation == {ZERO: Q(1), exp(0, 2): Q(-1)})

    return {
        "status": "passed",
        "arithmetic": "fractions.Fraction; exact rational arithmetic",
        "seed": 20260922,
        "checks_by_group": dict(sorted(counts.items())),
        "total_exact_assertions": sum(counts.values()),
        "scope": "Finite coefficient identities and finite prefixes only.",
        "not_verified_by_this_program": [
            "Infinite support well-ordering and arbitrary-rank Hom theorem",
            "Completion and cofinality classifications",
            "Spherical completeness or Hahn-Banach extension",
            "Existence of discontinuous Hamel functionals and invisible functionals",
            "Infinite-dimensional orthogonal-complement and missing-infimum claims",
            "Novelty or priority; no formal proof assistant was run"
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_report.json"))
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
