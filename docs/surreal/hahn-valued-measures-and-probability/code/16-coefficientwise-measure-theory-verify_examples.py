#!/usr/bin/env python3
"""Exact finite checks for Surreal-Valued Measure and Integration.

Arithmetic is in Q[e]/(e**(ORDER+1)); comparisons use the first nonzero
retained coefficient. These tests check finite algebra, not the infinite
measure-theoretic results or their hypotheses.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import json
from pathlib import Path
import platform
import random
from typing import Iterable, Sequence

ORDER = 8
SEED = 20260922
Series = tuple[F, ...]
ZERO: Series = (F(0),) * (ORDER + 1)
ONE: Series = (F(1),) + (F(0),) * ORDER
COUNTS: Counter[str] = Counter()


def series(coefficients: Iterable[int | F]) -> Series:
    values = tuple(F(x) for x in coefficients)
    if len(values) > ORDER + 1:
        raise ValueError("Too many coefficients for the truncation order")
    return values + (F(0),) * (ORDER + 1 - len(values))


def add(a: Series, b: Series) -> Series:
    return tuple(x + y for x, y in zip(a, b))


def scale(a: Series, c: int | F) -> Series:
    return tuple(F(c) * x for x in a)


def mul(a: Series, b: Series) -> Series:
    return tuple(sum((a[k] * b[n-k] for k in range(n + 1)), F(0))
                 for n in range(ORDER + 1))


def total(values: Iterable[Series]) -> Series:
    out = ZERO
    for value in values:
        out = add(out, value)
    return out


def inverse(a: Series) -> Series:
    if not a[0]:
        raise ValueError("Formal power-series inversion requires a nonzero constant")
    out = [1 / a[0]]
    for n in range(1, ORDER + 1):
        out.append(-sum((a[k] * out[n-k] for k in range(1, n+1)), F(0)) / a[0])
    return tuple(out)


def divide(a: Series, b: Series) -> Series:
    return mul(a, inverse(b))


def sign(a: Series) -> int:
    for value in a:
        if value:
            return 1 if value > 0 else -1
    return 0


def absolute(a: Series) -> Series:
    return scale(a, sign(a))


def check(group: str, predicate: bool, message: str) -> None:
    if not predicate:
        raise AssertionError(f"{group}: {message}")
    COUNTS[group] += 1


def expectation(weights: Sequence[Series], values: Sequence[Series]) -> Series:
    if len(weights) != len(values):
        raise ValueError("Weights and values must have equal lengths")
    return total(mul(p, f) for p, f in zip(weights, values))


def conditional(weights: Sequence[Series], values: Sequence[Series],
                blocks: Sequence[Sequence[int]]) -> list[Series]:
    indices = [i for block in blocks for i in block]
    if sorted(indices) != list(range(len(weights))):
        raise ValueError("Blocks must partition the indices")
    result = [ZERO] * len(weights)
    for block in blocks:
        value = divide(total(mul(weights[i], values[i]) for i in block),
                       total(weights[i] for i in block))
        for i in block:
            result[i] = value
    return result


def random_polynomial(rng: random.Random, degree: int = 3) -> Series:
    return series(F(rng.randint(-5, 5), rng.randint(1, 5)) for _ in range(degree+1))


def positive_weight(rng: random.Random) -> Series:
    return series([F(rng.randint(1, 7), rng.randint(1, 5))] +
                  [F(rng.randint(-4, 4), rng.randint(1, 4)) for _ in range(3)])


def set_partitions(items: tuple[int, ...]):
    """Each partition of a small finite set, without duplicate block orders."""
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for partition in set_partitions(rest):
        yield [(first,)] + partition
        for k in range(len(partition)):
            yield partition[:k] + [(first,) + partition[k]] + partition[k+1:]


def run_checks() -> dict:
    COUNTS.clear()
    rng = random.Random(SEED)
    for trial in range(40):
        weights = [positive_weight(rng) for _ in range(6)]
        mass = total(weights)
        probs = [divide(w, mass) for w in weights]
        values = [random_polynomial(rng) for _ in weights]
        check("normalization", total(probs) == ONE, f"total mass, trial {trial}")
        check("normalization", all(sign(p) > 0 for p in probs), "positive leading mass")
        check("formal inversion", mul(mass, inverse(mass)) == ONE, "unit inverse")

        targets = [random_polynomial(rng) for _ in weights]
        densities = [divide(v, w) for v, w in zip(targets, weights)]
        for i, (f, w, v) in enumerate(zip(densities, weights, targets)):
            check("finite Radon-Nikodym", mul(f, w) == v, f"point {i}")
        check("finite Radon-Nikodym", expectation(weights, densities) == total(targets),
              "whole-space identity")

        fine = [(0, 1), (2, 3), (4, 5)]
        coarse = [(0, 1, 2, 3), (4, 5)]
        conditioned = conditional(probs, values, fine)
        check("conditioning", expectation(probs, conditioned) == expectation(probs, values),
              "total expectation")
        check("conditioning", conditional(probs, conditioned, fine) == conditioned,
              "idempotence")
        check("conditioning", conditional(probs, conditioned, coarse) ==
              conditional(probs, values, coarse), "tower")
        for block in fine:
            check("conditioning", total(mul(probs[i], conditioned[i]) for i in block) ==
                  total(mul(probs[i], values[i]) for i in block), "event test")
        g = [random_polynomial(rng) for _ in fine]
        g_expanded = [g[i // 2] for i in range(6)]
        left = conditional(probs, [mul(x, y) for x, y in zip(g_expanded, values)], fine)
        right = [mul(x, y) for x, y in zip(g_expanded, conditioned)]
        check("conditioning", left == right, "measurable pull-out")

        other = [positive_weight(rng) for _ in range(3)]
        table = [[random_polynomial(rng) for _ in other] for _ in weights]
        direct = total(mul(mul(w, v), table[i][j])
                       for i, w in enumerate(weights) for j, v in enumerate(other))
        rows = [expectation(other, row) for row in table]
        columns = [expectation(weights, [table[i][j] for i in range(len(weights))])
                   for j in range(len(other))]
        check("finite Fubini", expectation(weights, rows) == direct, "row integration")
        check("finite Fubini", expectation(other, columns) == direct, "column integration")
        check("product mass", total(mul(w, v) for w in weights for v in other) ==
              mul(total(weights), total(other)), "rectangle mass")

        signed = [random_polynomial(rng) for _ in range(4)]
        plus = [x if sign(x) >= 0 else ZERO for x in signed]
        minus = [scale(x, -1) if sign(x) < 0 else ZERO for x in signed]
        variation = total(absolute(x) for x in signed)
        check("Hahn-Jordan", add(total(plus), scale(total(minus), -1)) == total(signed),
              "signed reconstruction")
        sign_partition_value = add(absolute(total(plus)), absolute(scale(total(minus), -1)))
        check("Hahn-Jordan", sign_partition_value == variation, "attainment")
        for partition in set_partitions(tuple(range(4))):
            candidate = total(absolute(total(signed[i] for i in block)) for block in partition)
            check("variation partitions", sign(add(variation, scale(candidate, -1))) >= 0,
                  "finite-partition bound")

        # Compare the displayed covariance formula to independent series division.
        real_p = [F(rng.randint(1, 5)) for _ in range(5)]
        real_p = [x / sum(real_p) for x in real_p]
        a = [F(rng.randint(-6, 6)) for _ in real_p]
        b = [F(rng.randint(-6, 6)) for _ in real_p]
        f = [F(rng.randint(-6, 6)) for _ in real_p]
        mean = lambda v: sum((p*x for p, x in zip(real_p, v)), F(0))
        numerator = series([mean(f), mean([x*y for x, y in zip(f, a)]),
                            mean([x*y for x, y in zip(f, b)])])
        denominator = series([1, mean(a), mean(b)])
        quotient = divide(numerator, denominator)
        predicted_1 = mean([x*y for x, y in zip(f, a)]) - mean(f)*mean(a)
        predicted_2 = (mean([x*y for x, y in zip(f, b)]) -
                       mean(a)*mean([x*y for x, y in zip(f, a)]) +
                       mean(f)*(mean(a)**2-mean(b)))
        check("conditioning expansion", quotient[1] == predicted_1, "covariance term")
        check("conditioning expansion", quotient[2] == predicted_2, "second-order term")

    # The bulk + two-atom law from the article.
    mean_x = divide(series([F(1, 2), 0, 1]), series([1, 1, 1]))
    check("worked probability", mean_x[:5] == (F(1,2), F(-1,2), F(1), F(-1,2), F(-1,2)),
          "coordinate expectation coefficients")
    point_one_given_atoms = divide(series([0, 1]), series([1, 1]))
    check("worked probability", point_one_given_atoms ==
          series([0] + [(-1)**(n-1) for n in range(1, ORDER+1)]), "rare-event conditioning")

    # Conditioning-domain counterexample: integrate after cancellation vs before.
    for n in range(1, 41):
        g = inverse(series([2, n]))
        weighted_zero = g
        weighted_one = mul(g, series([1, n]))
        check("conditioning obstruction", scale(add(weighted_zero, weighted_one), F(1,2)) ==
              series([F(1,2)]), "fiber cancellation")
        check("conditioning obstruction", weighted_zero[2] == F(n*n, 8) and
              weighted_one[2] == -F(n*n, 8), "opposite second-order coefficients")
        check("conditioning obstruction", (abs(weighted_zero[2])+abs(weighted_one[2])) /
              (2*n**3) == F(1, 8*n), "harmonic absolute-variation term")
        # Laurent support obstruction: independent monomial multiplication.
        exponent_of_mu, exponent_of_density = n, -n
        coefficient_of_mu, coefficient_of_density = F(1), F(1, 2**n)
        check("RN support obstruction", exponent_of_mu + exponent_of_density == 0 and
              coefficient_of_mu*coefficient_of_density == F(1, 2**n),
              "weighted Laurent singleton identity")

    return {
        "status": "PASS",
        "assertions": sum(COUNTS.values()),
        "groups": dict(sorted(COUNTS.items())),
        "arithmetic": f"exact rational coefficients modulo epsilon^{ORDER+1}",
        "truncation_order": ORDER,
        "random_seed": SEED,
        "random_trials": 40,
        "python_version": platform.python_version(),
        "scope": "Finite identities and example coefficients only; no verification of infinite proofs, convergence, or Lean code."
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the JSON verification record")
    args = parser.parse_args()
    result = run_checks()
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
