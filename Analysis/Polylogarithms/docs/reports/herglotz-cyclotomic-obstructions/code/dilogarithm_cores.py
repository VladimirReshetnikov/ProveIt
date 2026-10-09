#!/usr/bin/env python3
"""Construct rational dilogarithm cores for rational Herglotz values.

The result is a core C(p/q) for which F(p/q)-F(1)-C(p/q) is a combination
of products of logarithms of algebraic numbers and rational multiples of
pi^2. The logarithmic remainder is NOT computed by this program.

The mathematical guarantee is in the standard rational pre-Bloch/five-term
calculus. A failed congruence test is a formal obstruction, not a numerical
transcendence claim. All arithmetic in this implementation is exact.

Examples:
    python code/dilogarithm_cores.py 5 13
    python code/dilogarithm_cores.py 10 33 --output data/core_10_33.json
    python code/dilogarithm_cores.py

With no positional arguments the bundled example set is checked and saved
to data/dilogarithm_cores.json. Prime-coordinate verification uses trial
division and is intended for modest inputs; --no-prime-certificate omits
that optional check for large integers without changing the core algorithm.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from math import gcd
from pathlib import Path


def admissible_signs(numerator: int, modulus: int) -> list[int]:
    return [sign for sign in (1, -1) if (numerator*numerator - sign) % modulus == 0]


def reducible(p: int, q: int) -> bool:
    return bool(admissible_signs(p, q) and admissible_signs(q, p))


def _increasing_core(a: int, b: int) -> tuple[list[tuple[Fraction, Fraction]], list[dict]]:
    assert 1 <= a <= b and gcd(a, b) == 1 and reducible(a, b)
    if a == 1:
        return [], [{"action": "reciprocal_integer_base", "numerator": a, "denominator": b}]
    if b == a + 1:
        return [(Fraction(1), Fraction(a, b))], [
            {"action": "consecutive_shortcut", "numerator": a, "denominator": b}]
    signs = admissible_signs(a, b)
    # Since b>2 here, the larger modulus admits at most one of the signs.
    assert len(signs) == 1
    sign = signs[0]
    c = (a*a - sign) // b
    assert 1 <= c < a and gcd(c, a) == 1 and reducible(c, a)
    core, trace = _increasing_core(c, a)
    if sign == -1:
        coefficient, argument = Fraction(1, 2), Fraction(a*a, a*a + 1)
    else:
        coefficient, argument = Fraction(-1, 2), Fraction(a*a - 1, a*a)
    assert 0 < argument < 1
    core.append((coefficient, argument))
    trace.append({"action": "descent_step", "numerator": a, "denominator": b,
                  "square_sign": sign, "next_pair": [c, a],
                  "factorization_identity": {"a_squared_minus_sign": a*a - sign,
                                             "b_times_c": b*c},
                  "coefficient": str(coefficient), "argument": str(argument)})
    return core, trace


def construct_core(p: int, q: int) -> tuple[Fraction, list[tuple[Fraction, Fraction]], list[dict]]:
    if p <= 0 or q <= 0:
        raise ValueError("The numerator and denominator must be positive")
    ratio = Fraction(p, q)
    p, q = ratio.numerator, ratio.denominator
    if not reducible(p, q):
        raise ValueError("The rational-dilogarithm congruence conditions fail")
    if p <= q:
        core, trace = _increasing_core(p, q)
    else:
        core, trace = _increasing_core(q, p)
        core = [(-coefficient, argument) for coefficient, argument in core]
        trace.append({"action": "reciprocity", "input_pair": [p, q],
                      "reciprocal_pair": [q, p], "core_multiplier": -1})
    return ratio, core, trace


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


def prime_vector(value: Fraction | int) -> dict[int, int]:
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


def serial_wedge(value: dict[tuple[int, int], Fraction]) -> list[dict]:
    return [{"left_prime": pair[0], "right_prime": pair[1], "coefficient": str(coefficient)}
            for pair, coefficient in sorted(value.items())]


def verify_prime_boundary(p: int, q: int, core: list[tuple[Fraction, Fraction]]) -> dict:
    boundary = defaultdict(Fraction)
    for coefficient, argument in core:
        for pair, value in wedge(prime_vector(argument), prime_vector(1-argument)).items():
            boundary[pair] += coefficient*value
    boundary = {pair: value for pair, value in boundary.items() if value}
    target = {pair: -value for pair, value in wedge(prime_vector(p), prime_vector(q)).items()}
    difference = defaultdict(Fraction, boundary)
    for pair, value in target.items():
        difference[pair] -= value
    difference = {pair: value for pair, value in difference.items() if value}
    assert not difference, (p, q, difference)
    return {"verified": True,
            "numerator_prime_vector": prime_vector(p),
            "denominator_prime_vector": prime_vector(q),
            "core_boundary": serial_wedge(boundary),
            "target_boundary": serial_wedge(target),
            "difference": serial_wedge(difference)}


def result_for(p: int, q: int, prime_certificate: bool = True) -> dict:
    if p <= 0 or q <= 0:
        raise ValueError("The numerator and denominator must be positive")
    ratio = Fraction(p, q)
    a, b = ratio.numerator, ratio.denominator
    result = {"input_pair": [p, q], "reduced_pair": [a, b],
              "numerator_square_signs_mod_denominator": admissible_signs(a, b),
              "denominator_square_signs_mod_numerator": admissible_signs(b, a)}
    if not reducible(a, b):
        return {**result, "status": "formal_obstruction", "core": None,
                "meaning": "No rational-dilogarithm reduction in the stated five-term calculus; "
                           "this does not establish numerical nonreducibility."}
    _, core, trace = construct_core(a, b)
    result.update({"status": "rational_core_constructed",
                   "meaning": "F(p/q)-F(1)-core is a logarithmic combination; "
                              "the logarithmic remainder is not computed here.",
                   "core": [{"coefficient": str(coefficient), "argument": str(argument)}
                            for coefficient, argument in core],
                   "term_count": len(core), "trace": trace})
    if prime_certificate:
        result["prime_boundary_certificate"] = verify_prime_boundary(a, b, core)
    return result


def example_results() -> dict:
    pairs = [(1, 7), (6, 7), (4, 17), (2, 5), (5, 13), (3, 8), (10, 33),
             (13, 5), (2, 7), (11, 8), (7, 15), (8, 3), (89, 233),
             (144, 233), (3, 10), (21, 55), (987, 988), (1000, 999)]
    examples = [result_for(p, q) for p, q in pairs]
    # Concrete independently derived cores specified in the article.
    expected = {
        (5, 13): [(Fraction(1, 2), Fraction(4, 5)), (Fraction(1, 2), Fraction(25, 26))],
        (3, 8): [(Fraction(-1, 2), Fraction(8, 9))],
        (10, 33): [(Fraction(1, 2), Fraction(9, 10)), (Fraction(-1, 2), Fraction(99, 100))],
        (6, 7): [(Fraction(1), Fraction(6, 7))],
    }
    for pair, value in expected.items():
        assert construct_core(*pair)[1] == value
    return {"example_count": len(examples),
            "constructed_core_count": sum(item["status"] == "rational_core_constructed" for item in examples),
            "formal_obstruction_count": sum(item["status"] == "formal_obstruction" for item in examples),
            "examples": examples}


def verify_up_to(bound: int) -> dict:
    """Check every admissible coprime pair and its reciprocal up to bound."""
    count, max_terms, max_examples = 0, 0, []
    for a in range(1, bound + 1):
        for b in range(a, bound + 1):
            if gcd(a, b) != 1 or not reducible(a, b):
                continue
            _, core, _ = construct_core(a, b)
            verify_prime_boundary(a, b, core)
            _, inverse_core, _ = construct_core(b, a)
            verify_prime_boundary(b, a, inverse_core)
            assert inverse_core == [(-c, x) for c, x in core]
            if len(core) > max_terms:
                max_terms, max_examples = len(core), [[a, b]]
            elif len(core) == max_terms:
                max_examples.append([a, b])
            count += 1
    return {"bound": bound, "admissible_pairs": count,
            "rational_boundaries_verified_in_both_orientations": 2*count,
            "max_core_term_count": max_terms,
            "max_term_count_examples": max_examples}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("p", type=int, nargs="?")
    parser.add_argument("q", type=int, nargs="?")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--no-prime-certificate", action="store_true")
    parser.add_argument("--verify-bound", type=int, default=0,
                        help="Also check all admissible pairs and reciprocals up to this bound")
    args = parser.parse_args()
    if (args.p is None) != (args.q is None):
        parser.error("Supply both p and q, or neither")
    if args.p is None:
        result = example_results()
        if args.verify_bound:
            if args.verify_bound < 2:
                parser.error("--verify-bound must be at least 2")
            result["exhaustive_check"] = verify_up_to(args.verify_bound)
        destination = args.output or Path(__file__).resolve().parents[1] / "data" / "dilogarithm_cores.json"
    else:
        try:
            result = result_for(args.p, args.q, not args.no_prime_certificate)
        except ValueError as error:
            parser.error(str(error))
        destination = args.output
    if destination is not None:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    if args.p is None:
        print(json.dumps({key: value for key, value in result.items() if key != "examples"}, indent=2))
    else:
        print(json.dumps(result, indent=2))
