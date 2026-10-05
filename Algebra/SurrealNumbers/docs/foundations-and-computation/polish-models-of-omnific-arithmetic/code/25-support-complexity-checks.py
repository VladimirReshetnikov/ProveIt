#!/usr/bin/env python3
"""Finite exact checks for the accompanying research article.

These are regression tests for finite formulas, not proofs of infinitary
well-foundedness, descriptive-set-theoretic completeness, or Lean correctness.
Only Python's standard library is required. All arithmetic is rational.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from random import Random
from typing import Callable, Dict, Mapping, Tuple

Position = Tuple[int, int]  # (nonnegative row index, integer Hahn exponent)
Array = Dict[Position, Fraction]
ZERO = Fraction(0)
ONE = Fraction(1)


@dataclass(frozen=True)
class Name:
    """A finite real-certified array over Gamma = Z."""

    coefficients: Array
    support_bound: Fraction
    incidence_bounds: Dict[int, Fraction]


def height(exponent: int) -> int:
    """The cut height for Z, using c_j = -j."""
    return max(0, -exponent)


def soft_threshold(value: Fraction, stage: int) -> Fraction:
    if stage < 1:
        raise ValueError("The regularization stage must be positive.")
    magnitude = max(abs(value) - Fraction(2, stage), ZERO)
    return magnitude if value >= 0 else -magnitude


def ramp(value: Fraction, stage: int) -> Fraction:
    if stage < 1:
        raise ValueError("The regularization stage must be positive.")
    return min(ONE, Fraction(stage, 2) * abs(value))


def regularize(raw: Mapping[Position, Fraction], stage: int) -> Name:
    """Use E_k = {(n,g): 0 <= n < k and |g| <= k}.

    Sparse entries outside this finite window are ignored. A finite stage of
    an explicitly given infinite input can be supplied by its finite window.
    """
    if stage < 1:
        raise ValueError("The regularization stage must be positive.")
    coefficients: Array = {}
    bound = ZERO
    incidence: Dict[int, Fraction] = {}
    for (row, exponent), value in raw.items():
        if row < 0:
            raise ValueError("Row indices must be nonnegative.")
        if row >= stage or abs(exponent) > stage:
            continue
        weight = ramp(value, stage)
        bound = max(bound, height(exponent) * weight)
        incidence[exponent] = max(incidence.get(exponent, ZERO), row * weight)
        transformed = soft_threshold(value, stage)
        if transformed:
            coefficients[(row, exponent)] = transformed
    return Name(coefficients, bound, incidence)


def validate(name: Name) -> None:
    assert name.support_bound >= 0
    assert all(value >= 0 for value in name.incidence_bounds.values())
    for (row, exponent), value in name.coefficients.items():
        assert value != 0
        assert height(exponent) <= name.support_bound
        assert row <= name.incidence_bounds.get(exponent, ZERO)


def coefficient_sum(raw: Mapping[Position, Fraction]) -> Dict[int, Fraction]:
    result: Dict[int, Fraction] = {}
    for (_, exponent), value in raw.items():
        result[exponent] = result.get(exponent, ZERO) + value
    return {exponent: value for exponent, value in result.items() if value}


def b_less(left: Position, right: Position) -> bool:
    n, m = left
    nn, mm = right
    return n < nn or (n == nn and m > mm)


def group_embedding(point: Position) -> Tuple[int, int]:
    n, m = point
    return (n + 1, -m - 1)  # a = (1,0), u = (0,1) in lexicographic Z^2


def check_order_embedding() -> int:
    points = [(n, m) for n in range(8) for m in range(8)]
    comparisons = 0
    for left in points:
        for right in points:
            assert b_less(left, right) == (group_embedding(left) < group_embedding(right))
            comparisons += 1
    assert len({group_embedding(point) for point in points}) == len(points)
    return comparisons


def check_random_regularizations() -> Tuple[int, int, int]:
    rng = Random(20261004)
    cases = 200
    stages = (1, 2, 4, 8, 16, 32, 64)
    stage_checks = 0
    observation_checks = 0
    for _ in range(cases):
        raw: Array = {}
        for _ in range(45):
            position = (rng.randrange(12), rng.randrange(-8, 9))
            value = Fraction(rng.randrange(-5, 6), rng.randrange(1, 8))
            if value:
                raw[position] = value
        names = [regularize(raw, stage) for stage in stages]
        for name in names:
            validate(name)
            stage_checks += 1
        for before, after in zip(names, names[1:]):
            assert before.support_bound <= after.support_bound
            for exponent in range(-8, 9):
                assert before.incidence_bounds.get(exponent, ZERO) <= after.incidence_bounds.get(
                    exponent, ZERO
                )

        exact_support_bound = max([0] + [height(g) for (_, g), x in raw.items() if x])
        exact_incidence = {
            g: max([0] + [n for (n, gg), x in raw.items() if gg == g and x])
            for g in range(-8, 9)
        }
        # All coordinates are included by stage 32; every nonzero input has
        # magnitude >= 1/7, so its ramp is exactly 1 at stages 32 and 64.
        for name in names[-2:]:
            assert name.support_bound == exact_support_bound
            for g, expected in exact_incidence.items():
                assert name.incidence_bounds.get(g, ZERO) == expected
        final = names[-1]
        for position, value in raw.items():
            assert abs(final.coefficients.get(position, ZERO) - value) <= Fraction(2, 64)

        # An insertion beyond every observed row preserves all observations
        # but shifts a selected output coefficient by exactly one.
        observations = [(rng.randrange(15), rng.randrange(-8, 9)) for _ in range(25)]
        far_row = max(n for n, _ in observations) + 10
        changed = dict(raw)
        key = (far_row, 0)
        changed[key] = changed.get(key, ZERO) + ONE
        for position in observations:
            assert changed.get(position, ZERO) == raw.get(position, ZERO)
            observation_checks += 1
        assert coefficient_sum(changed).get(0, ZERO) - coefficient_sum(raw).get(0, ZERO) == ONE
    return cases, stage_checks, observation_checks


def window_of(rule: Callable[[int, int], Fraction], stage: int) -> Array:
    return {
        (n, g): value
        for n in range(stage)
        for g in range(-stage, stage + 1)
        if (value := rule(n, g)) != 0
    }


def check_divergence_patterns() -> Tuple[list[int], list[int]]:
    stages = [2, 4, 8, 16, 32, 64]
    incidence_values: list[int] = []
    support_values: list[int] = []
    for stage in stages:
        repeated = window_of(lambda n, g: ONE if g == 0 else ZERO, stage)
        repeated_name = regularize(repeated, stage)
        validate(repeated_name)
        assert repeated_name.support_bound == 0
        assert repeated_name.incidence_bounds[0] == stage - 1
        incidence_values.append(int(repeated_name.incidence_bounds[0]))

        descending = window_of(lambda n, g: ONE if g == -(n + 1) else ZERO, stage)
        descending_name = regularize(descending, stage)
        validate(descending_name)
        assert descending_name.support_bound == stage
        support_values.append(int(descending_name.support_bound))
    return incidence_values, support_values


def main() -> None:
    comparisons = check_order_embedding()
    cases, stage_checks, observations = check_random_regularizations()
    incidence_values, support_values = check_divergence_patterns()
    print("Exact finite regression checks -- all passed")
    print("Seed: 20261004; arithmetic: fractions.Fraction; external dependencies: none")
    print(f"B -> lexicographic Z^2: {comparisons} pairwise order comparisons")
    print(f"Finite rational arrays: {cases}")
    print(f"Certified regularization stages validated: {stage_checks}")
    print("Least bounds: exact at stages 32 and 64 in every random case")
    print(f"Unchanged raw observations in sum-perturbation tests: {observations}")
    print("Stages for explicit infinite-input windows: [2, 4, 8, 16, 32, 64]")
    print(f"Repeated contributions at exponent 0, incidence bounds: {incidence_values}")
    print(f"Descending exponents -(n+1), support bounds: {support_values}")
    print("Scope: finite formulas only; no infinitary or Lean proof verification.")


if __name__ == "__main__":
    main()
