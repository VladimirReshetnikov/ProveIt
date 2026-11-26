#!/usr/bin/env python3
"""Exact-arithmetic checks for the torsion-selection research note.

These checks validate recurrence identities, conservative constants, finite
cyclotomic examples, and explicit obstructions.  They do NOT constitute a
Lean formalization or a numerical proof of the general p-adic theorem.
Only Python's standard library is required.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import random


def radius(p: int, h: int) -> Q:
    assert h >= 1
    return Q(1, (p - 1) * p ** (h - 1))


def ceilq(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def exact_bound(p: int, h0: int, budget: Q) -> int:
    assert budget >= 0
    return h0 + ceilq(p ** h0 * budget * (h0 + budget + 2))


def positive_bound(p: int, h0: int, budget: Q, tolerance: Q) -> int:
    assert tolerance > 0 and budget >= 0
    t0 = h0 + budget + tolerance + 1
    kappa = 1 - Q(1, p - 1) / (t0 + 1)
    assert kappa > Q(1, 2)
    return h0 + ceilq(budget * t0 / (kappa * tolerance))


def equality_weights(p: int, hstart: int, C: Q, state_Q: Q, z: Q, count: int):
    """Yield (h,u,d,Q,z_before) in the equality comparison recurrence."""
    q, c = Q(1, p), 1 - Q(1, p)
    for h in range(hstart, hstart + count):
        t = h + C
        u = state_Q / t
        d = u - c * z
        yield h, u, d, state_Q, z
        next_z = q * z + u
        next_Q = state_Q + c * next_z
        next_u = next_Q / (t + 1)
        next_d = next_u - c * next_z
        assert next_u - u == -q * d / (t + 1)
        assert next_d == q * t / (t + 1) * d
        state_Q, z = next_Q, next_z


def check_recurrences() -> int:
    cases = 0
    for p, h0, B, delta in product(
        (2, 3, 5, 7), (1, 2, 4),
        (Q(0), Q(1, 10), Q(1), Q(3, 2), Q(5)),
        (Q(1, 100), Q(1, 3), Q(1), Q(2)),
    ):
        C = B + delta + 1
        t0 = h0 + C
        kappa = 1 - Q(1, p - 1) / (t0 + 1)
        for j, (_, u, d, _, _) in enumerate(
            equality_weights(p, h0, C, delta, Q(0), 35)
        ):
            assert d == delta * Q(1, p) ** j / (t0 + j)
            assert u >= kappa * delta / t0
        H = positive_bound(p, h0, B, delta)
        assert (H - h0 + 1) * kappa * delta / t0 > B
        cases += 1

    for p, h0, B in product(
        (2, 3, 5, 7), (1, 2, 4),
        (Q(0), Q(1, 10), Q(1), Q(3, 2), Q(5)),
    ):
        a, c, C = radius(p, h0), 1 - Q(1, p), B + 1
        assert c * a == Q(1, p ** h0)
        t1 = h0 + B + 2
        previous_u = Q(0)
        for _, u, d, _, _ in equality_weights(p, h0 + 1, C, c * a, a, 35):
            assert d < 0
            assert u >= c * a / t1
            assert u >= previous_u
            previous_u = u
        H = exact_bound(p, h0, B)
        assert a + (H - h0) * c * a / t1 > B
        cases += 1

    # Componentwise monotonic comparison with strict larger actual weights.
    rng = random.Random(20261125)
    for p, hstart in product((2, 3, 5), (1, 2, 5)):
        q, c = Q(1, p), 1 - Q(1, p)
        C = Q(7, 3)
        min_Q, min_z = Q(2, 7), Q(1, 9)
        actual_Q, actual_z = min_Q, min_z
        for h in range(hstart, hstart + 40):
            min_w = min_Q / (h + C)
            actual_w = actual_Q / (h + C) + Q(rng.randrange(1, 8), 97)
            assert actual_w > min_w
            min_z = q * min_z + min_w
            actual_z = q * actual_z + actual_w
            min_Q += c * min_z
            actual_Q += c * actual_z
            assert actual_Q > min_Q and actual_z > min_z
        cases += 1
    return cases


def primitive_exponents(p: int, h: int):
    return [a for a in range(1, p ** h) if a % p]


def cyclotomic_difference(p: int, left: tuple[int, int], right: tuple[int, int]):
    """Valuation of zeta_(p^h)^a - zeta_(p^k)^b; None denotes infinity.

    All roots are chosen in one compatible cyclotomic tower.  Results are
    rational and follow exactly from v(zeta_(p^j)-1)=1/phi(p^j).
    """
    h, a = left
    k, b = right
    n = max(h, k)
    difference = (a * p ** (n - h) - b * p ** (n - k)) % (p ** n)
    if difference == 0:
        return None
    exponent = 0
    while difference % p == 0:
        difference //= p
        exponent += 1
    return radius(p, n - exponent)


def monic_value(p: int, roots, point):
    result = Q(0)
    for root in roots:
        distance = cyclotomic_difference(p, point, root)
        if distance is None:
            return None
        result += distance
    return result


def monic_gauss(p: int, roots, rho: Q):
    return sum((min(rho, radius(p, h)) for h, _ in roots), Q(0))


def check_shell_averaging() -> int:
    cases = 0
    for p, h, C in product((2, 3, 5, 7), range(1, 6), (Q(1, 3), Q(1), Q(4))):
        a = radius(p, h)
        capped = Q(0)
        exponents = primitive_exponents(p, h)
        for k in exponents:
            distance = cyclotomic_difference(p, (h, k), (h, 1))
            capped += C if distance is None else min(distance - a, C)
        average = capped / len(exponents)
        assert average <= a * (h + C)
        if C >= 1:
            assert average == a * (C + h - 1 - Q(1, p - 1) + a)
        cases += 1
    return cases


def check_examples() -> dict:
    rng = random.Random(12359)
    examples = 0
    largest_first_good = 0
    for p in (2, 3, 5):
        for h0 in (1, 2, 3):
            rho = radius(p, h0)
            for _ in range(45):
                roots = []
                for _ in range(rng.randrange(1, 15)):
                    h = rng.randrange(h0, h0 + 5)
                    exponent = rng.choice(primitive_exponents(p, h))
                    roots.append((h, exponent))
                A = monic_gauss(p, roots, rho)
                H = exact_bound(p, h0, A)
                # A shell beyond every root valuation always works, so no
                # search of irrelevant enormously large upper bounds is needed.
                search_end = min(H, max(h for h, _ in roots) + 1)
                witness = None
                for h in range(h0, search_end + 1):
                    for exponent in primitive_exponents(p, h):
                        value = monic_value(p, roots, (h, exponent))
                        if value is not None and value <= A:
                            witness = (h, exponent, value)
                            break
                    if witness:
                        break
                assert witness is not None
                largest_first_good = max(largest_first_good, witness[0])
                examples += 1

    # Exact counterexamples for two tempting but false strengthenings.
    obstruction_cases = 0
    for L in range(1, 10):
        roots = [(h, 1) for h in range(1, L + 1)]
        original_gauss = monic_gauss(2, roots, Q(1))
        assert original_gauss == 2 - Q(1, 2 ** (L - 1)) < 2
        for h in range(1, L + 1):
            moving_gauss = monic_gauss(2, roots, radius(2, h))
            for exponent in primitive_exponents(2, h):
                value = monic_value(2, roots, (h, exponent))
                assert value is None or value > moving_gauss
                # At least the corresponding individual factor fails its own
                # fixed-rho Gauss bound throughout this shell.
                individual = cyclotomic_difference(2, (h, exponent), (h, 1))
                assert individual is None or individual > radius(2, h)
        obstruction_cases += 1

    return {
        "finite_cyclotomic_polynomial_examples": examples,
        "largest_first_successful_shell_in_examples": largest_first_good,
        "counterexample_packets": obstruction_cases,
    }


def bound_table():
    rows = []
    for p, h0, B, delta in (
        (2, 2, Q(1), Q(1, 10)),
        (3, 2, Q(1), Q(1, 100)),
        (5, 2, Q(2), Q(1, 100)),
        (3, 3, Q(6), Q(1, 1000)),
        (2, 1, Q(1, 4), Q(1, 100)),
    ):
        rows.append({
            "p": p, "h0": h0, "B": str(B), "delta": str(delta),
            "r_h0": str(radius(p, h0)),
            "H_exact_safe": exact_bound(p, h0, B),
            "H_positive_safe": positive_bound(p, h0, B, delta),
            "first_shell_all_good_if_B_lt_radius": B < radius(p, h0),
        })
    return rows


def main():
    report = {
        "purpose": "Exact-arithmetic checks supporting a human proof; not a Lean verification.",
        "recurrence_cases": check_recurrences(),
        "shell_averaging_cases": check_shell_averaging(),
        "examples": check_examples(),
        "bounds": bound_table(),
        "status": "all assertions passed",
    }
    output = Path(__file__).with_name("exact_torsion_checks.json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
