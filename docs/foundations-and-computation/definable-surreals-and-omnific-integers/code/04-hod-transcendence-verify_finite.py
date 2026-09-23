#!/usr/bin/env python3
"""Finite regression checks for Definable Surreal Numbers and Omnific Integers.

This program manipulates finite formal tags and exact rational numbers.
It is NOT a surreal arithmetic implementation, a definability decision
procedure, a model of HOD, or a proof of the transfinite theorems.
No numerical replacement of omega is made.

Usage:
    python verify_finite.py --output verification_results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Term:
    # None denotes exponent 1 (the leading omega term).
    # n >= 0 denotes the formal exponent e_n = omega^(-(n+1)).
    exponent: int | None
    coefficient: Fraction


Code = tuple[Term, ...]
MultiIndex = tuple[int, ...]
Exponent = tuple[int, ...]
CoefficientSeries = dict[int, Fraction]
Polynomial = dict[MultiIndex, CoefficientSeries]


def encode(signs: str) -> Code:
    """Encode a FINITE sign word using the self-delimiting coefficient code."""
    if not isinstance(signs, str) or any(sign not in "+-" for sign in signs):
        raise ValueError("The input must be a finite string over '+' and '-'.")
    tail = tuple(Term(n, Fraction(2 if s == "+" else 1))
                 for n, s in enumerate(signs))
    return (Term(None, Fraction(1)), *tail,
            Term(len(signs), Fraction(3)))


def decode(code: Code) -> str:
    """Validate and invert a finite formal code, rejecting malformed inputs."""
    if not isinstance(code, tuple) or len(code) < 2:
        raise ValueError("A code needs a leading term and an end marker.")
    if any(not isinstance(term, Term) for term in code):
        raise ValueError("Every entry must be a Term.")
    if code[0] != Term(None, Fraction(1)):
        raise ValueError("The leading term must be exactly omega.")
    tail = code[1:]
    for n, term in enumerate(tail):
        if type(term.exponent) is not int or term.exponent != n:
            raise ValueError("Tail exponents must be e_0,...,e_alpha in order.")
        if not isinstance(term.coefficient, Fraction):
            raise ValueError("Coefficients must be exact Fraction objects.")
    if tail[-1].coefficient != 3:
        raise ValueError("The last coefficient must be the end marker 3.")
    if any(term.coefficient not in (1, 2) for term in tail[:-1]):
        raise ValueError("A sign coefficient must be 1 or 2.")
    return "".join("+" if term.coefficient == 2 else "-"
                   for term in tail[:-1])


def finite_code_tests(max_length: int) -> dict[str, int]:
    seen: set[Code] = set()
    count = 0
    for n in range(max_length + 1):
        for letters in itertools.product("-+", repeat=n):
            word = "".join(letters)
            code = encode(word)
            assert decode(code) == word
            assert code not in seen
            assert len(code) == n + 2
            assert all(term.coefficient in (1, 2, 3) for term in code)
            assert all(term.exponent is not None for term in code[1:])
            seen.add(code)
            count += 1
    malformed: list[Code] = [
        (),
        (Term(None, Fraction(1)),),
        (Term(None, Fraction(2)), Term(0, Fraction(3))),
        (Term(None, Fraction(1)), Term(1, Fraction(3))),
        (Term(None, Fraction(1)), Term(0, Fraction(2))),
        (Term(None, Fraction(1)), Term(0, Fraction(3)), Term(1, Fraction(3))),
        (Term(None, Fraction(1)), Term(0, Fraction(0)), Term(1, Fraction(3))),
        (Term(None, Fraction(1)), Term(0, Fraction(4)), Term(1, Fraction(3))),
        (Term(None, Fraction(1)), Term(0, Fraction(2)), Term(0, Fraction(3))),
        (Term(None, Fraction(1)), Term(0, Fraction(2)), Term(2, Fraction(3))),
        (Term(None, Fraction(1)), Term(None, Fraction(3))),
    ]
    for code in malformed:
        try:
            decode(code)
        except ValueError:
            continue
        raise AssertionError(f"Malformed code was accepted: {code!r}")
    return {"maximum_finite_sign_length": max_length,
            "round_trip_and_injectivity_cases": count,
            "malformed_codes_rejected": len(malformed)}


def h(x: Fraction) -> Fraction:
    return (1 + x / (1 + abs(x))) / 4


def inverse_h(g: Fraction) -> Fraction:
    if not 0 < g < Fraction(1, 2):
        raise ValueError("The inverse domain is (0,1/2).")
    u = 4 * g - 1
    return u / (1 - abs(u))


def rational_tests() -> dict[str, int]:
    points = sorted({Fraction(n, d) for n in range(-100, 101)
                     for d in range(1, 26)})
    images = [h(x) for x in points]
    for x, g in zip(points, images):
        assert 0 < g < Fraction(1, 2)
        assert inverse_h(g) == x
    assert all(a < b for a, b in zip(images, images[1:]))
    for endpoint in (Fraction(0), Fraction(1, 2)):
        try:
            inverse_h(endpoint)
        except ValueError:
            pass
        else:
            raise AssertionError("An excluded endpoint was accepted.")
    return {"two_term_code_rational_normalizations": len(points),
            "strict_order_comparisons": len(points) - 1,
            "excluded_endpoints_rejected": 2}


def lex_compare(a: tuple[Fraction, int], b: tuple[Fraction, int]) -> int:
    """Compare rational + integer*epsilon in formal lexicographic order."""
    return (a > b) - (a < b)


def floor_tests() -> dict[str, int]:
    points = {Fraction(n, d) for n in range(-50, 51) for d in range(1, 12)}
    count = 0
    for r in points:
        for epsilon_sign in (-1, 0, 1):
            z = r.numerator // r.denominator
            if r.denominator == 1 and epsilon_sign < 0:
                z -= 1
            x = (r, epsilon_sign)
            assert lex_compare((Fraction(z), 0), x) <= 0
            assert lex_compare(x, (Fraction(z + 1), 0)) < 0
            count += 1
    return {"formal_floor_boundary_cases": count}


def evaluate_formal(poly: Polynomial, generators: tuple[Exponent, ...]
                    ) -> dict[Exponent, Fraction]:
    """Evaluate in a finite group algebra, not in the full surreal field.

    The first exponent coordinate represents a coefficient-subgroup
    direction. Remaining coordinates represent the quotient by that subgroup.
    """
    if not generators or len({len(g) for g in generators}) != 1:
        raise ValueError("Generators need one common positive dimension.")
    dimension = len(generators[0])
    if dimension < 1:
        raise ValueError("Exponent dimension must be positive.")
    result: dict[Exponent, Fraction] = {}
    for multi, coefficient in poly.items():
        if len(multi) != len(generators) or any(m < 0 for m in multi):
            raise ValueError("Invalid polynomial multi-index.")
        shift = tuple(sum(multi[j] * generators[j][k]
                          for j in range(len(generators)))
                      for k in range(dimension))
        for base, value in coefficient.items():
            exponent = (shift[0] + base, *shift[1:])
            result[exponent] = result.get(exponent, Fraction(0)) + value
    return {key: value for key, value in result.items() if value}


def support_coset_tests() -> dict[str, int]:
    rng = random.Random(20260923)
    trials = 0
    checked_terms = 0
    for number_of_variables in range(1, 6):
        # Standard basis vectors in the quotient, with coefficient coordinate 0.
        generators = tuple((0, *(int(j == k) for k in range(number_of_variables)))
                           for j in range(number_of_variables))
        for _ in range(100):
            poly: Polynomial = {}
            for _ in range(40):
                multi = tuple(rng.randrange(5) for _ in range(number_of_variables))
                coeff: CoefficientSeries = {}
                for base in rng.sample(range(-10, 11), rng.randrange(1, 8)):
                    value = Fraction(rng.choice([-5, -3, -1, 1, 2, 4]),
                                     rng.randrange(1, 6))
                    coeff[base] = value
                poly[multi] = coeff
            result = evaluate_formal(poly, generators)
            # In independent cosets no two polynomial terms share a support point.
            expected = sum(len(coeff) for coeff in poly.values())
            assert result and len(result) == expected
            checked_terms += expected
            trials += 1
    # Negative control: g_2 = 2*g_1, so Y_2 - Y_1^2 really does vanish.
    dependent = ((0, 1), (0, 2))
    relation: Polynomial = {(0, 1): {0: Fraction(1)},
                            (2, 0): {0: Fraction(-1)}}
    assert evaluate_formal(relation, dependent) == {}
    return {"independent_coset_polynomials": trials,
            "noncancelled_formal_support_terms": checked_terms,
            "dependent_exponent_negative_controls": 1}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-length", type=int, default=12,
                        help="Maximum finite sign-word length (default: 12).")
    parser.add_argument("--output", type=Path,
                        help="Optional JSON result file.")
    args = parser.parse_args()
    if not 0 <= args.max_length <= 18:
        parser.error("--max-length must lie between 0 and 18.")
    results = {
        "status": "passed",
        "scope": "Finite formal regression checks only; not a proof of HOD or transfinite claims.",
        "code_checks": finite_code_tests(args.max_length),
        "rational_checks": rational_tests(),
        "floor_checks": floor_tests(),
        "support_coset_checks": support_coset_tests(),
        "random_seed": 20260923,
    }
    text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
