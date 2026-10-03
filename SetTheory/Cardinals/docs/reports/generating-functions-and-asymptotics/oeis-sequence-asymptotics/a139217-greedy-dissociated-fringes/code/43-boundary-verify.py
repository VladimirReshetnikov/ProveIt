#!/usr/bin/env python3
"""Exact verification for the A139217/A139218 research note.

The script uses only Python's standard library.  It independently:
  * generates the residue-restricted greedy dissociated sequences;
  * computes their signed difference sets exactly;
  * verifies the finite boundary-defect invariants;
  * checks the closed forms, recurrences, and generating-function prefixes;
  * checks the exact staircase counting formulas.

This is a reproducibility aid, not a substitute for the proofs in article.tex.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence


def signed_difference_set(values: Iterable[int]) -> set[int]:
    """Return {sum eps_i a_i : eps_i in {-1,0,1}} exactly."""
    out = {0}
    for value in values:
        out = {x + eps * value for x in out for eps in (-1, 0, 1)}
    return out


def greedy_residue_sequence(modulus: int, residue: int, terms: int) -> list[int]:
    """Generate the least positive admissible term in one residue class."""
    if modulus < 2:
        raise ValueError("modulus must be at least 2")
    residue %= modulus
    values: list[int] = []
    differences = {0}
    candidate = residue if residue > 0 else modulus
    while len(values) < terms:
        if candidate not in differences:
            values.append(candidate)
            differences = {
                x + eps * candidate for x in differences for eps in (-1, 0, 1)
            }
        candidate += modulus
    return values


def boundary_model(total: int, offsets: Sequence[int]) -> set[int]:
    holes = {sign * (total - c) for sign in (-1, 1) for c in offsets}
    return set(range(-total, total + 1)) - holes


def u_closed(n: int) -> int:
    if n < 3:
        return (1, 4)[n - 1]
    periodic = {0: 1, 1: 1, 2: -2}[n % 3]
    return 3 * 2 ** (n - 2) + periodic


def v_closed(n: int) -> int:
    if n < 4:
        return (2, 5, 8)[n - 1]
    periodic = {
        0: Fraction(-25, 7),
        1: Fraction(20, 7),
        2: Fraction(5, 7),
    }[n % 3]
    value = Fraction(39, 56) * 2**n + periodic
    assert value.denominator == 1
    return value.numerator


def phi(y: Fraction) -> int:
    """max(0,floor(log_8 y)), with value 0 for y <= 0.

    The implementation avoids floating-point boundary errors by comparing powers.
    """
    if y <= 0:
        return 0
    k = 0
    power = Fraction(1)
    while power * 8 <= y:
        power *= 8
        k += 1
    return k


def count_u(x: int) -> int:
    return (
        int(x >= 1)
        + int(x >= 4)
        + phi(Fraction(4 * (x - 1), 3))
        + phi(Fraction(2 * (x - 1), 3))
        + phi(Fraction(x + 2, 3))
    )


def count_v(x: int) -> int:
    return (
        int(x >= 2)
        + int(x >= 5)
        + int(x >= 8)
        + phi(Fraction(7 * x + 25, 39))
        + phi(Fraction(28 * x - 80, 39))
        + phi(Fraction(14 * x - 10, 39))
    )



def rational_series_coefficients(numerator: Sequence[int], terms: int) -> list[int]:
    """Expand P(z)/(1-z-z^2-2z^3) through the requested number of terms.

    ``numerator[n]`` is the coefficient of z^n; index 0 is allowed.
    """
    coefficients = [0] * (terms + 1)
    for n in range(1, terms + 1):
        value = numerator[n] if n < len(numerator) else 0
        if n >= 1:
            value += coefficients[n - 1]
        if n >= 2:
            value += coefficients[n - 2]
        if n >= 3:
            value += 2 * coefficients[n - 3]
        coefficients[n] = value
    return coefficients[1:]

def recurrence_ok(values: Sequence[int], start_n: int) -> bool:
    """Check a(n)=a(n-1)+a(n-2)+2a(n-3) for one-based n>=start_n."""
    for n in range(start_n, len(values) + 1):
        if values[n - 1] != values[n - 2] + values[n - 3] + 2 * values[n - 4]:
            return False
    return True


def verify_boundary_propagation(offsets: Sequence[int], d: int, total: int) -> None:
    old = boundary_model(total, offsets)
    appended = total - d
    new_total = total + appended
    propagated = {x + eps * appended for x in old for eps in (-1, 0, 1)}
    expected = boundary_model(new_total, offsets)
    assert propagated == expected


def main() -> None:
    number_of_terms = 17
    u = greedy_residue_sequence(3, 1, number_of_terms)
    v = greedy_residue_sequence(3, 2, number_of_terms)

    expected_u_prefix = [1, 4, 7, 13, 22, 49, 97, 190, 385, 769, 1534, 3073]
    expected_v_prefix = [2, 5, 8, 14, 23, 41, 92, 179, 353, 716, 1427, 2849]
    assert u[: len(expected_u_prefix)] == expected_u_prefix
    assert v[: len(expected_v_prefix)] == expected_v_prefix

    # Exact boundary-defect invariants.
    for n in range(3, number_of_terms + 1):
        prefix = u[:n]
        assert signed_difference_set(prefix) == boundary_model(sum(prefix), [3])
    for n in range(3, number_of_terms + 1):
        prefix = v[:n]
        assert signed_difference_set(prefix) == boundary_model(sum(prefix), [1, 3, 6, 11])

    # Closed forms, partial sums, recurrence ranges, and generating functions.
    assert all(value == u_closed(n) for n, value in enumerate(u, start=1))
    assert all(value == v_closed(n) for n, value in enumerate(v, start=1))
    assert recurrence_ok(u, 6)
    assert recurrence_ok(v, 7)
    assert u[4] != u[3] + u[2] + 2 * u[1]  # A139217's displayed n>4 range fails at n=5.

    for n in range(3, number_of_terms + 1):
        q = {0: 0, 1: 1, 2: -1}[n % 3]
        assert sum(u[:n]) == 3 * 2 ** (n - 1) + q
        correction = {0: -1, 1: -4, 2: 5}[n % 3]
        if n < number_of_terms:
            assert u[n] - 2 * u[n - 1] == correction

    for n in range(4, number_of_terms + 1):
        s_periodic = {
            0: Fraction(27, 7),
            1: Fraction(47, 7),
            2: Fraction(52, 7),
        }[n % 3]
        assert Fraction(sum(v[:n])) == Fraction(39, 28) * 2**n + s_periodic
        correction = {0: 10, 1: -5, 2: -5}[n % 3]
        if n < number_of_terms:
            assert v[n] - 2 * v[n - 1] == correction
        cross = {0: -63, 1: 27, 2: 36}[n % 3]
        assert 14 * v[n - 1] - 13 * u[n - 1] == cross

    u_numerator = [0, 1, 3, 2, 0, -6]
    v_numerator = [0, 2, 3, 1, -3, -9, -12]
    assert rational_series_coefficients(u_numerator, number_of_terms) == u
    assert rational_series_coefficients(v_numerator, number_of_terms) == v

    # Boundary-propagation theorem, sampled over all offsets used in the proofs.
    for total in (12, 25, 47, 96, 193):
        for d in (-1, 3, -2):
            if total > 2 * 3 + abs(d):
                verify_boundary_propagation([3], d, total)
    for total in (29, 52, 93, 185, 364):
        for d in (1, 6, 11):
            if total > 2 * 11 + abs(d):
                verify_boundary_propagation([1, 3, 6, 11], d, total)

    # Exact counting functions on a large interval.
    for x in range(0, u[-1] + 1):
        assert count_u(x) == sum(value <= x for value in u)
    for x in range(0, v[-1] + 1):
        assert count_v(x) == sum(value <= x for value in v)

    print("All exact checks passed.")
    print("A139217 prefix:", u)
    print("A139218 prefix:", v)
    print("A139217 boundary offsets: {3}")
    print("A139218 boundary offsets: {1, 3, 6, 11}")
    print("A139217 recurrence begins at n=6; the OEIS n>4 wording fails at n=5.")
    print("A139218 recurrence begins at n=7, as conjectured in OEIS.")
    print("Closed forms, partial sums, generating functions, cross-relations, and counting formulas checked.")


if __name__ == "__main__":
    main()
