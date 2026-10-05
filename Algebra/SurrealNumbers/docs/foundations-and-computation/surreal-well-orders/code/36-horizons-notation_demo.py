#!/usr/bin/env python3
"""Finite natural-coefficient hereditary Omega normal forms.

This is a small executable syntax/comparison demonstrator for the accompanying
article, not a proof assistant or an implementation of proper classes. A term
is an immutable tuple of (exponent_term, positive_natural_coefficient) tuples.
The exponents are strictly decreasing, recursively, and the empty tuple is 0.

Only NATURAL coefficients are implemented. The article permits arbitrary
positive set ordinals; that larger grammar is not implemented here. In
particular, Omega denotes the article's formal Ord symbol, not the missing
set-ordinal constant omega. No addition, multiplication, or exponentiation of
arbitrary input order presentations is implemented.

Python 3.10 or later; standard library only.
"""

from __future__ import annotations

import argparse
import itertools
import json
import platform
import random
from pathlib import Path
from typing import Callable, Iterable, TypeAlias, cast

Term: TypeAlias = tuple[tuple["Term", int], ...]


class InvalidTerm(ValueError):
    """The supplied object is not a canonical term in this restricted grammar."""


def _compare_valid(left: Term, right: Term) -> int:
    """Structural comparison; the caller must establish validity first."""
    for (left_exp, left_coeff), (right_exp, right_coeff) in zip(left, right):
        exponent_comparison = _compare_valid(left_exp, right_exp)
        if exponent_comparison:
            return exponent_comparison
        if left_coeff != right_coeff:
            return 1 if left_coeff > right_coeff else -1
    return (len(left) > len(right)) - (len(left) < len(right))


def validate(candidate: object) -> Term:
    """Recursively check shape, natural coefficients, and normal form.

    Return the unchanged immutable term on success; raise InvalidTerm otherwise.
    Exact tuples and exact ints are required: mutable lists and bool coefficients
    are rejected. Python's ordinary recursion limit applies to extremely deep
    inputs; it is an implementation bound, not a mathematical bound.
    """

    def visit(node: object, location: str) -> Term:
        if type(node) is not tuple:
            raise InvalidTerm(f"{location}: a term must be an immutable tuple")
        previous: Term | None = None
        for index, pair in enumerate(node):
            pair_location = f"{location}[{index}]"
            if type(pair) is not tuple or len(pair) != 2:
                raise InvalidTerm(f"{pair_location}: expected a two-element tuple")
            exponent, coefficient = pair
            checked_exponent = visit(exponent, f"{pair_location}.exponent")
            if type(coefficient) is not int or coefficient <= 0:
                raise InvalidTerm(
                    f"{pair_location}.coefficient: expected a positive natural"
                )
            if previous is not None and _compare_valid(previous, checked_exponent) <= 0:
                raise InvalidTerm(
                    f"{pair_location}: exponents must be strictly decreasing"
                )
            previous = checked_exponent
        return cast(Term, node)

    return visit(candidate, "root")


def is_valid(candidate: object) -> bool:
    """Return whether an ordinary bounded-depth input is a canonical term."""
    try:
        validate(candidate)
    except InvalidTerm:
        return False
    return True


def compare(left: object, right: object) -> int:
    """Return -1, 0, or 1 after independently validating both input terms."""
    return _compare_valid(validate(left), validate(right))


def make_term(pairs: Iterable[tuple[Term, int]]) -> Term:
    """Build a checked term; do not sort, combine, or silently normalize it."""
    return validate(tuple(pairs))


ZERO: Term = ()


def natural(value: int) -> Term:
    """The canonical constant for a nonnegative natural number."""
    if type(value) is not int or value < 0:
        raise ValueError("a natural constant requires an exact nonnegative int")
    return ZERO if value == 0 else ((ZERO, value),)


def monomial(exponent: Term, coefficient: int = 1) -> Term:
    """Construct the syntactic expression Omega^exponent * coefficient."""
    return make_term(((exponent, coefficient),))


ONE = natural(1)
OMEGA = monomial(ONE)
OMEGA_TO_OMEGA = monomial(OMEGA)


def tower_boundary(index: int) -> Term:
    """w_0 = Omega and w_(n+1) = Omega^(w_n), for a natural index n.

    The paper proves that w_n bounds all full-grammar terms of height <= n+1.
    This program constructs the boundary's syntax, but its restricted coefficient
    language does not enumerate that full predecessor class.
    """
    if type(index) is not int or index < 0:
        raise ValueError("the tower index must be an exact nonnegative int")
    result = OMEGA
    for _ in range(index):
        result = monomial(result)
    return result


def height(term: Term) -> int:
    """Finite syntax height; zero has height 0 and positive constants height 1."""
    checked = validate(term)

    def visit(node: Term) -> int:
        return 0 if not node else 1 + max(visit(exponent) for exponent, _ in node)

    return visit(checked)


def pretty(term: Term) -> str:
    """Print explicit hereditary Omega notation without evaluating class orders."""
    checked = validate(term)

    def visit(node: Term) -> str:
        if not node:
            return "0"
        parts: list[str] = []
        for exponent, coefficient in node:
            if exponent == ZERO:
                parts.append(str(coefficient))
                continue
            if exponent == ONE:
                power = "Ω"
            elif len(exponent) == 1 and exponent[0][0] == ZERO:
                power = f"Ω^{exponent[0][1]}"
            elif exponent == OMEGA:
                power = "Ω^Ω"
            else:
                power = f"Ω^({visit(exponent)})"
            parts.append(power if coefficient == 1 else f"{power}·{coefficient}")
        return " + ".join(parts)

    return visit(checked)


def finite_radix_oracle(term: object, base: int, *, max_exponent: int = 128) -> int:
    """An INDEPENDENT exact natural-number evaluator for bounded tests only.

    Replace the formal Omega symbol everywhere by a single finite base b, then
    evaluate sum(b ** evaluated_exponent * coefficient). This routine calls
    neither validate() nor either structural comparison routine. It checks raw
    shape and coefficient bounds, but deliberately does not check normal form:
    ordinary-natural evaluation is independent of the comparison under test.

    Correct comparison via this oracle requires b > every coefficient in every
    tested term, including exponent subtrees. It is not class-order semantics.
    The exponent cap prevents accidental evaluation of huge integer towers.
    """
    if type(base) is not int or base < 2:
        raise ValueError("the oracle base must be an exact int at least 2")
    if type(max_exponent) is not int or max_exponent < 0:
        raise ValueError("max_exponent must be an exact nonnegative int")

    def evaluate(raw: object) -> int:
        if type(raw) is not tuple:
            raise ValueError("oracle input must use tuple nodes")
        result = 0
        for entry in raw:
            if type(entry) is not tuple or len(entry) != 2:
                raise ValueError("oracle input must use exponent/coefficient pairs")
            exponent, coefficient = entry
            if type(coefficient) is not int or not 0 < coefficient < base:
                raise ValueError("the oracle requires 0 < coefficient < base")
            exponent_value = evaluate(exponent)
            if exponent_value > max_exponent:
                raise ValueError("oracle exponent cap exceeded; evaluation stopped")
            result += pow(base, exponent_value) * coefficient
        return result

    return evaluate(term)


def _expect_rejection(operation: Callable[..., object], *arguments: object) -> None:
    """Small test helper; do not rely on Python's removable assert statement."""
    try:
        operation(*arguments)
    except (InvalidTerm, ValueError):
        return
    raise AssertionError("a malformed input was incorrectly accepted")


def _check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def verify() -> dict[str, object]:
    """Run deterministic structural and independent finite-radix checks."""
    base = 7
    max_coefficient = 4
    seed = 20261004
    named_checks: list[str] = []

    # These targeted checks specify the intended comparison decisions directly.
    omega_plus_one = make_term(((ONE, 1), (ZERO, 1)))
    omega_plus_two = make_term(((ONE, 1), (ZERO, 2)))
    omega_times_two = monomial(ONE, 2)
    omega_squared = monomial(natural(2))
    _check(compare(ZERO, ONE) == -1, "zero is below a nonzero term")
    named_checks.append("zero_before_nonzero")
    _check(compare(OMEGA, omega_plus_one) == -1, "proper prefix must be smaller")
    _check(compare(omega_plus_one, OMEGA) == 1, "reverse prefix comparison")
    named_checks.append("proper_prefix_both_directions")
    _check(compare(omega_plus_one, omega_plus_two) == -1, "tail coefficient")
    _check(compare(OMEGA, omega_times_two) == -1, "leading coefficient")
    named_checks.append("equal_exponent_coefficient_decision")
    large_tail = make_term(((ONE, 1000), (ZERO, 1000)))
    _check(compare(large_tail, omega_squared) == -1, "leading exponent dominance")
    named_checks.append("leading_exponent_dominates_large_finite_tail")
    _check(compare(OMEGA_TO_OMEGA, tower_boundary(1)) == 0, "canonical equality")
    named_checks.append("canonical_equality")
    for index in range(7):
        boundary = tower_boundary(index)
        _check(height(boundary) == index + 2, "tower syntax height")
        _check(compare(boundary, tower_boundary(index + 1)) == -1, "tower ordering")
    named_checks.append("eight_tower_boundaries_structural_only")
    _check(pretty(ZERO) == "0", "zero printing")
    _check(pretty(natural(123)) == "123", "constant printing")
    _check(pretty(OMEGA) == "Ω", "Omega printing")
    _check(pretty(OMEGA_TO_OMEGA) == "Ω^Ω", "Omega-to-Omega printing")
    _check(pretty(tower_boundary(2)) == "Ω^(Ω^Ω)", "nested exponent printing")
    named_checks.append("prettyprinting_examples")

    malformed: list[object] = [
        [],
        1,
        "0",
        ([],),
        ((ZERO,),),
        ((ZERO, 1, 2),),
        ([ZERO, 1],),
        ((1, 1),),
        ((ZERO, 0),),
        ((ZERO, -1),),
        ((ZERO, True),),
        ((ZERO, 1.0),),
        ((ZERO, "1"),),
        ((ZERO, 1), (ONE, 1)),
        ((ONE, 1), (ONE, 2)),
        ((((ZERO, 0),), 1),),
    ]
    for raw in malformed:
        _check(not is_valid(raw), "is_valid accepted malformed input")
        _expect_rejection(validate, raw)
        _expect_rejection(compare, raw, ZERO)
        _expect_rejection(compare, ZERO, raw)
    for invalid_natural in (-1, True, 1.0):
        _expect_rejection(natural, invalid_natural)
        _expect_rejection(tower_boundary, invalid_natural)
    named_checks.append("malformed_shape_coefficients_order_and_nested_nodes")

    # Exhaust all digit vectors with four available natural exponents 0,...,3
    # and digits 0,...,4. The construction uses an ordinary descending integer
    # range, not the comparison routine being tested.
    shallow: list[Term] = []
    for digits in itertools.product(range(max_coefficient + 1), repeat=4):
        shallow.append(
            tuple(
                (natural(exponent), digits[exponent])
                for exponent in range(3, -1, -1)
                if digits[exponent]
            )
        )

    # Build deeper terms using ONLY independent integer evaluation to order the
    # selected exponent trees. Bound every evaluated exponent by 48, so the
    # largest tested top-level integer is small (less than 7**49).
    exponent_pool = [
        (finite_radix_oracle(term, base), term)
        for term in shallow
        if finite_radix_oracle(term, base) <= 48
    ]
    rng = random.Random(seed)
    nested: set[Term] = set()
    while len(nested) < 384:
        selected = rng.sample(exponent_pool, rng.randint(1, 4))
        selected.sort(key=lambda pair: pair[0], reverse=True)
        nested.add(
            tuple((term, rng.randint(1, max_coefficient)) for _, term in selected)
        )
    samples = list(dict.fromkeys(shallow + list(nested)))
    # Sort only by the independent oracle, making the report deterministic even
    # if Python's set iteration order changes between interpreter versions.
    samples.sort(key=lambda term: finite_radix_oracle(term, base))
    values = [finite_radix_oracle(term, base) for term in samples]
    _check(len(values) == len(set(values)), "independent evaluations collided")
    for term in samples:
        _check(validate(term) is term, "validation must preserve immutable identity")
        _check(compare(term, term) == 0, "reflexive comparison")

    pair_count = 0
    for i, left in enumerate(samples):
        for j in range(i + 1, len(samples)):
            expected = (values[i] > values[j]) - (values[i] < values[j])
            _check(compare(left, samples[j]) == expected, "finite-radix disagreement")
            pair_count += 1

    reverse_pair_checks = 2000
    for _ in range(reverse_pair_checks):
        i, j = rng.sample(range(len(samples)), 2)
        expected = (values[i] > values[j]) - (values[i] < values[j])
        _check(compare(samples[i], samples[j]) == expected, "reverse comparison")
    named_checks.append("all_sample_pairs_against_independent_exact_natural_values")

    _expect_rejection(finite_radix_oracle, natural(base), base)
    _expect_rejection(finite_radix_oracle, tower_boundary(2), base)
    named_checks.append("oracle_rejects_bad_radix_and_huge_towers")

    return {
        "status": "passed",
        "program": "notation_demo.py",
        "python_version": platform.python_version(),
        "coefficient_domain": "positive natural numbers only",
        "term_representation": "immutable recursive tuples",
        "random_seed": seed,
        "independent_oracle": {
            "method": "exact ordinary-natural evaluation at one common finite radix",
            "base": base,
            "maximum_coefficient_in_oracle_samples": max_coefficient,
            "exhaustive_shallow_samples": len(shallow),
            "generated_nested_samples_before_union": len(nested),
            "distinct_total_samples": len(samples),
            "maximum_syntax_height": max(height(term) for term in samples),
            "largest_evaluated_integer_bit_length": max(values).bit_length(),
            "unordered_pair_checks": pair_count,
            "additional_ordered_pair_checks": reverse_pair_checks,
            "reflexive_checks": len(samples),
            "validation_identity_checks": len(samples),
            "distinct_evaluations": len(set(values)),
        },
        "malformed_inputs_rejected": len(malformed),
        "named_checks": named_checks,
        "examples": {
            "zero": pretty(ZERO),
            "natural_seventeen": pretty(natural(17)),
            "Omega": pretty(OMEGA),
            "Omega_to_Omega": pretty(OMEGA_TO_OMEGA),
            "w_2": pretty(tower_boundary(2)),
            "w_3": pretty(tower_boundary(3)),
            "mixed_term": pretty(
                make_term(((OMEGA, 2), (natural(3), 4), (ZERO, 3)))
            ),
        },
        "limitations": [
            "Finite tests do not prove class well-foundedness or any theorem in the paper.",
            "This is not a Lean formalization, or any other proof-assistant formalization.",
            "Natural coefficients omit all infinite set-ordinal constants and coefficients.",
            "The fragment is not closed under the whole ordinal arithmetic of the paper; "
            "arbitrary ordinal-indexed sums and arbitrary ordinal coefficients leave it.",
            "The finite-radix oracle is a test device, not the interpretation of Omega as Ord.",
            "Tower boundaries beyond the bounded oracle range are tested structurally only.",
            "No arithmetic on arbitrary class order presentations is implemented.",
            "Python's ordinary recursion and memory limits apply.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report", type=Path, help="write the deterministic verification results as JSON"
    )
    parser.add_argument(
        "--examples-only", action="store_true", help="print examples without running tests"
    )
    args = parser.parse_args()
    if args.examples_only:
        if args.report:
            parser.error("--report requires verification; omit --examples-only")
        for name, term in (
            ("0", ZERO),
            ("17", natural(17)),
            ("Omega", OMEGA),
            ("Omega^Omega", OMEGA_TO_OMEGA),
            ("w_2", tower_boundary(2)),
            ("w_3", tower_boundary(3)),
        ):
            print(f"{name}: {pretty(term)}")
        return
    report = verify()
    if args.report:
        args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
