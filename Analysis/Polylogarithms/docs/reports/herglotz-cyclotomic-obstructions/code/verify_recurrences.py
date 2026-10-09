#!/usr/bin/env python3
"""Exact verification of the rational Herglotz recurrence classification.

This script compares a complete bounded search for the two square-congruence
conditions with the three recurrence families proved in the accompanying
article. It also checks the rational dilogarithm cores in the exterior square
of Q^* tensor Q, using exact rational arithmetic on prime-exponent vectors.

This is supplemental finite verification. It is not a proof of completeness
outside the stated bound or a numerical transcendence test.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from math import gcd
from pathlib import Path


def square_conditions(a: int, b: int) -> bool:
    """The unordered pair is assumed positive, with a <= b."""
    return (gcd(a, b) == 1
            and ((a*a - 1) % b == 0 or (a*a + 1) % b == 0)
            and ((b*b - 1) % a == 0 or (b*b + 1) % a == 0))


def recurrence_families(bound: int) -> dict[tuple[int, int], dict]:
    """Return one shortest recurrence certificate for every generated pair."""
    pairs: dict[tuple[int, int], dict] = {}

    def record(family: str, parameter: int, terms: list[int]) -> None:
        a, b = terms[-2:]
        candidate = {"family": family, "parameter": parameter,
                     "index": len(terms) - 2, "terms": terms.copy()}
        old = pairs.get((a, b))
        if old is None or candidate["index"] < old["index"]:
            pairs[(a, b)] = candidate

    # Both square congruences have sign +1.
    for parameter in range(2, bound + 1):
        terms = [1, parameter]
        while terms[-1] <= bound:
            record("minus_recurrence", parameter, terms)
            terms.append(parameter*terms[-1] - terms[-2])

    # Mixed signs alternate along the recurrence; parameter 1 is Fibonacci.
    for parameter in range(1, bound + 1):
        terms = [1, parameter]
        while terms[-1] <= bound:
            record("plus_recurrence", parameter, terms)
            terms.append(parameter*terms[-1] + terms[-2])

    # Both signs -1: consecutive odd-index Fibonacci numbers.
    terms = [1, 2]
    while terms[-1] <= bound:
        record("odd_fibonacci", 3, terms)
        terms.append(3*terms[-1] - terms[-2])
    return pairs


def rational_core(certificate: dict) -> list[tuple[Fraction, Fraction]]:
    """Pairs (coefficient, argument), all arguments strictly between 0 and 1."""
    terms = certificate["terms"]
    core = []
    for j in range(1, len(terms) - 1):
        value = terms[j]
        epsilon = value*value - terms[j-1]*terms[j+1]
        assert epsilon in (-1, 1)
        if epsilon == -1:
            core.append((Fraction(1, 2), Fraction(value*value, value*value + 1)))
        else:
            core.append((Fraction(-1, 2), Fraction(value*value - 1, value*value)))
    assert all(0 < argument < 1 for _, argument in core)
    return core


@lru_cache(maxsize=None)
def factor(number: int) -> tuple[tuple[int, int], ...]:
    assert number > 0
    result = []
    divisor = 2
    while divisor*divisor <= number:
        exponent = 0
        while number % divisor == 0:
            number //= divisor
            exponent += 1
        if exponent:
            result.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if number > 1:
        result.append((number, 1))
    return tuple(result)


def multiplicative_vector(value: Fraction | int) -> dict[int, int]:
    value = Fraction(value)
    assert value > 0
    result = defaultdict(int)
    for prime, exponent in factor(value.numerator):
        result[prime] += exponent
    for prime, exponent in factor(value.denominator):
        result[prime] -= exponent
    return {prime: exponent for prime, exponent in result.items() if exponent}


def wedge(left: dict[int, int], right: dict[int, int]) -> dict[tuple[int, int], Fraction]:
    result = defaultdict(Fraction)
    for p, x in left.items():
        for q, y in right.items():
            if p < q:
                result[(p, q)] += x*y
            elif q < p:
                result[(q, p)] -= x*y
    return {pair: value for pair, value in result.items() if value}


@lru_cache(maxsize=None)
def dilog_boundary(argument: Fraction) -> tuple[tuple[tuple[int, int], Fraction], ...]:
    return tuple(wedge(multiplicative_vector(argument),
                       multiplicative_vector(1-argument)).items())


def verify_core(a: int, b: int, core: list[tuple[Fraction, Fraction]]) -> None:
    actual = defaultdict(Fraction)
    for coefficient, argument in core:
        for pair, value in dilog_boundary(argument):
            actual[pair] += coefficient*value
    actual = {pair: value for pair, value in actual.items() if value}
    target = {pair: -value for pair, value in
              wedge(multiplicative_vector(a), multiplicative_vector(b)).items()}
    assert actual == target, (a, b, actual, target)


def run(bound: int, data_dir: Path) -> dict:
    generated = recurrence_families(bound)
    enumerated = {(a, b) for a in range(1, bound + 1)
                  for b in range(a, bound + 1) if square_conditions(a, b)}
    missing = sorted(enumerated - generated.keys())
    extra = sorted(generated.keys() - enumerated)
    assert not missing and not extra, {"missing": missing, "extra": extra}

    rows = []
    selected_families = Counter()
    for (a, b), certificate in sorted(generated.items()):
        core = rational_core(certificate)
        verify_core(a, b, core)
        selected_families[certificate["family"]] += 1
        rows.append({"numerator": a, "denominator": b,
                     "family": certificate["family"],
                     "parameter": certificate["parameter"],
                     "index": certificate["index"],
                     "core_term_count": len(core),
                     "rational_boundary_verified": True})

    example_pairs = [(2, 3), (2, 5), (3, 8), (3, 10), (4, 17),
                     (5, 12), (5, 13), (8, 21), (13, 34)]
    examples = []
    for pair in example_pairs:
        if pair not in generated:
            continue
        certificate = generated[pair]
        core = rational_core(certificate)
        examples.append({"numerator": pair[0], "denominator": pair[1],
                         **certificate,
                         "core": [{"coefficient": str(coefficient),
                                   "argument": str(argument)}
                                  for coefficient, argument in core]})

    summary = {"bound": bound, "search_region": "1 <= p <= q <= bound, gcd(p,q)=1",
               "matching_pair_count": len(enumerated),
               "missing_count": len(missing), "extra_count": len(extra),
               "rational_core_boundaries_verified": len(rows),
               "selected_certificate_family_counts": dict(selected_families),
               "examples": examples}
    data_dir.mkdir(parents=True, exist_ok=True)
    (data_dir / "recurrence_checks.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    with (data_dir / "recurrence_pairs.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bound", type=int, default=500)
    parser.add_argument("--data-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    arguments = parser.parse_args()
    if arguments.bound < 2:
        parser.error("--bound must be at least 2")
    result = run(arguments.bound, arguments.data_dir)
    print(json.dumps({key: value for key, value in result.items() if key != "examples"}, indent=2))
