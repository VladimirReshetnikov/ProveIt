#!/usr/bin/env python3
"""Finite illustrations for Class Well-Orders Beyond Ord.

This program verifies explicit finite instances of the support-splitting
and support-flattening maps and checks hereditary-term comparisons against
independent finite-base evaluation. It is not a proof of class well-foundedness.
Coefficients here are natural numbers, a strict fragment of the article.
Run: python3 artifacts/finite_notation_checks.py
"""

from dataclasses import dataclass
from functools import cmp_to_key
from itertools import product
from pathlib import Path
import json


@dataclass(frozen=True)
class Term:
    """Pairs (exponent, positive coefficient), in decreasing exponent order."""

    pairs: tuple = ()


ZERO = Term()


def compare(left: Term, right: Term) -> int:
    for (le, lc), (re, rc) in zip(left.pairs, right.pairs):
        c = compare(le, re)
        if c:
            return c
        if lc != rc:
            return (lc > rc) - (lc < rc)
    return (len(left.pairs) > len(right.pairs)) - (
        len(left.pairs) < len(right.pairs)
    )


def polynomial(*pairs) -> Term:
    """Construct a canonical polynomial; duplicate exponents are rejected."""
    nonzero = [(e, c) for e, c in pairs if c != 0]
    if any(not isinstance(c, int) or c < 0 for _, c in pairs):
        raise ValueError("This illustrative implementation requires natural coefficients")
    nonzero.sort(key=cmp_to_key(lambda x, y: -compare(x[0], y[0])))
    if any(compare(a[0], b[0]) == 0 for a, b in zip(nonzero, nonzero[1:])):
        raise ValueError("Duplicate exponent; supply the intended ordinal coefficient")
    return Term(tuple(nonzero))


def constant(n: int) -> Term:
    return polynomial((ZERO, n))


def monomial(exponent: Term) -> Term:
    return polynomial((exponent, 1))


ONE = constant(1)
OMEGA = monomial(ONE)


def evaluate(term: Term, base: int) -> int:
    """Exact finite-base interpretation, when all coefficients are < base."""
    if base < 2:
        raise ValueError("Base must be at least 2")
    value = 0
    for exponent, coefficient in term.pairs:
        if coefficient >= base:
            raise ValueError("Base must strictly exceed every coefficient")
        e = evaluate(exponent, base)
        if e > 10000:
            raise OverflowError("Example exceeds the deliberate evaluation resource bound")
        value += pow(base, e) * coefficient
    return value


def display(term: Term) -> str:
    if not term.pairs:
        return "0"
    parts = []
    for exponent, coefficient in term.pairs:
        if exponent == ZERO:
            parts.append(str(coefficient))
        else:
            base = "Omega" if exponent == ONE else f"Omega^({display(exponent)})"
            parts.append(base if coefficient == 1 else f"{base}*{coefficient}")
    return " + ".join(parts)


def digit_value(digits: tuple, base: int) -> int:
    return sum(d * pow(base, i) for i, d in enumerate(digits))


def digits_of(number: int, base: int, length: int) -> tuple:
    digits = []
    for _ in range(length):
        digits.append(number % base)
        number //= base
    if number:
        raise ValueError("Number does not fit the declared exponent set")
    return tuple(digits)


def run_checks() -> dict:
    split_count = 0
    flatten_count = 0
    for base in (2, 3):
        for b in range(4):
            for c in range(4):
                # a^(b+c) -> a^b * a^c, with the right block more significant.
                for digits in product(range(base), repeat=b + c):
                    lower, upper = digits[:b], digits[b:]
                    expected = digit_value(lower, base) + pow(base, b) * digit_value(upper, base)
                    assert digit_value(digits, base) == expected
                    assert lower + upper == digits
                    split_count += 1
                # (a^b)^c -> a^(b*c): outer coordinate first in significance.
                inner_base = pow(base, b)
                for outer in product(range(inner_base), repeat=c):
                    flat = tuple(d for value in outer for d in digits_of(value, base, b))
                    assert len(flat) == b * c
                    assert digit_value(outer, inner_base) == digit_value(flat, base)
                    flatten_count += 1

    omega_plus_one = polynomial((ONE, 1), (ZERO, 1))
    exponents = [ZERO, ONE, constant(2), constant(3), OMEGA, omega_plus_one]
    terms = {ZERO}
    for e in exponents:
        for coefficient in (1, 2, 3):
            terms.add(polynomial((e, coefficient)))
    for e in exponents[1:]:
        for coefficient in (1, 2):
            terms.add(polynomial((e, coefficient), (ZERO, 3)))
    terms.add(polynomial((OMEGA, 2), (constant(2), 3), (ZERO, 1)))
    ordered = sorted(terms, key=cmp_to_key(compare))
    comparison_count = 0
    for base in (5, 7, 11):
        values = {term: evaluate(term, base) for term in ordered}
        assert len(set(values.values())) == len(ordered)
        for left in ordered:
            for right in ordered:
                actual = (values[left] > values[right]) - (values[left] < values[right])
                assert compare(left, right) == actual
                comparison_count += 1

    return {
        "status": "passed",
        "scope": "Finite illustrations only; no class-theoretic proof or Lean verification",
        "power_split_instances": split_count,
        "power_flatten_instances": flatten_count,
        "hereditary_terms": len(ordered),
        "comparison_instances": comparison_count,
        "interpretation_bases": [5, 7, 11],
        "ordered_examples": [display(term) for term in ordered],
    }


if __name__ == "__main__":
    result = run_checks()
    destination = Path(__file__).with_name("finite_notation_results.json")
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items() if key != "ordered_examples"}, indent=2))
