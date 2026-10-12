#!/usr/bin/env python3
"""Exact finite checks for the even-order tail extension (standard library).

This program does not use the new generator to build comparison values.
1. It checks the cubic cutoff identity as a polynomial in an independent
   variable Z.  Thus the identity is tested before Z is set to zeta(2q).
2. It compares finite tail differences with independently constructed
   strict multiple harmonic sums, for all anchors used through power 5.
3. It computes the even-zeta factors by the Bernoulli recurrence.

These finite checks are diagnostics.  The accompanying TeX gives the
universal finite identity, the asymptotic bounds, and the limit proof.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb, factorial
from pathlib import Path


def harmonic(n: int, order: int) -> F:
    return sum((F(1, k**order) for k in range(1, n + 1)), F(0))


def shifted_power(h: F, degree: int) -> list[F]:
    """Coefficients of (Z-h)^degree in increasing powers of Z."""
    return [F(comb(degree, j)) * (-h) ** (degree - j)
            for j in range(degree + 1)] + [F(0)] * (3 - degree)


def add_scaled(target: list[F], value: list[F], scale: F | int) -> None:
    for j in range(4):
        target[j] += scale * value[j]


def check_cubic_cutoff(q: int, cutoff: int) -> dict:
    p = 2 * q
    left = [F(0)] * 4
    hn = F(0)
    for n in range(cutoff):
        add_scaled(left, shifted_power(hn, 3), (n + 1)**p - n**p)
        add_scaled(left, shifted_power(hn, 2), -3)
        hn += F(1, (n + 1)**p)

    right = [F(0)] * 4
    add_scaled(right, shifted_power(hn, 3), cutoff**p)
    add_scaled(right, shifted_power(hn, 2), F(3, 2))
    right[2] -= F(3, 2)
    right[0] -= harmonic(cutoff, 2 * p) / 2
    residual = [left[j] - right[j] for j in range(4)]
    assert residual == [F(0)] * 4, (q, cutoff, residual)
    return {"q": q, "cutoff": cutoff,
            "residual_coefficients": [str(x) for x in residual]}


def compositions(total: int):
    if total == 0:
        yield ()
    else:
        for first in range(1, total + 1):
            for rest in compositions(total - first):
                yield (first,) + rest


@lru_cache(maxsize=None)
def strict_harmonic(word: tuple[int, ...], cutoff: int) -> F:
    """Sum n1>...>nr>=1, n1<=cutoff, with positive integer indices."""
    if not word:
        return F(1)
    if cutoff < len(word):
        return F(0)
    first, rest = word[0], word[1:]
    return sum((F(1, n**first) * strict_harmonic(rest, n - 1)
                for n in range(1, cutoff + 1)), F(0))


def finite_anchor_from_differences(p: int, power: int, h: int,
                                   cutoff: int) -> F:
    """Use the finite tail sum_(n<k<=cutoff) k^-p, independently of MHS."""
    tail = harmonic(cutoff, p)
    result = F(0)
    for n in range(1, cutoff + 1):
        old_tail = tail
        tail -= F(1, n**p)
        result += F(n)**h * (old_tail**power - tail**power)
    assert tail == 0
    return result


def finite_anchor_from_compositions(p: int, power: int, h: int,
                                    cutoff: int) -> F:
    result = F(0)
    for parts in compositions(power):
        multiplicity = factorial(power)
        for part in parts:
            multiplicity //= factorial(part)
        # Compute the multinomial directly as a Fraction as an additional
        # guard against any intermediate integer-division convention.
        exact_multiplicity = F(factorial(power))
        for part in parts:
            exact_multiplicity /= factorial(part)
        assert exact_multiplicity.denominator == 1
        assert multiplicity == exact_multiplicity
        word = tuple(p * a for a in parts[:-1]) + (p * parts[-1] - h,)
        assert all(s >= 1 for s in word)
        result += multiplicity * strict_harmonic(word, cutoff)
    return result


def needed_anchors(p: int, max_power: int) -> set[tuple[int, int]]:
    anchors = set()
    for d in range(1, max_power + 1):
        for k in range(1, p):
            if (k - d - 1) % 2 == 0:
                anchors.add((d, k))
        for j in range(1, (d - 1) // 2 + 1):
            for k in range(p, 2 * p * j + 1):
                if (k - d - 1) % 2 == 0:
                    anchors.add((d - 2 * j, k - 2 * p * j))
    assert (1, p - 1) not in anchors
    return anchors


def bernoulli_numbers(max_index: int) -> list[F]:
    values = [F(1)]
    for n in range(1, max_index + 1):
        values.append(-sum((F(comb(n + 1, k)) * values[k]
                            for k in range(n)), F(0)) / (n + 1))
    return values


def run() -> dict:
    cubic = [check_cubic_cutoff(q, cutoff)
             for q in range(1, 5) for cutoff in (1, 2, 5, 9)]
    anchors = []
    for q in range(1, 5):
        p = 2 * q
        for power, h in sorted(needed_anchors(p, 5)):
            # Convergence of the infinite anchor is proved separately.
            assert h < (p - 1) * power
            for cutoff in (3, 6):
                left = finite_anchor_from_differences(p, power, h, cutoff)
                right = finite_anchor_from_compositions(p, power, h, cutoff)
                assert left == right, (q, power, h, cutoff, left - right)
                anchors.append({"q": q, "power": power, "h": h,
                                "cutoff": cutoff, "value": str(left),
                                "residual": "0"})

    bernoulli = bernoulli_numbers(16)
    assert bernoulli[1] == F(-1, 2)

    def zeta_pi_coefficient(k: int) -> F:
        return F((-1)**(k + 1) * 2**(2 * k - 1), factorial(2 * k)) \
            * bernoulli[2 * k]

    euler_factors = []
    for q in range(1, 5):
        ratio = zeta_pi_coefficient(q)**2 / zeta_pi_coefficient(2 * q)
        cubic_factor = -(3 * ratio + 1) / 2
        euler_factors.append({"q": q, "zeta_2q_squared_over_zeta_4q": str(ratio),
                              "cubic_right_side_coefficient_of_zeta_4q":
                              str(cubic_factor)})
    assert euler_factors[1]["zeta_2q_squared_over_zeta_4q"] == "7/6"
    assert euler_factors[1]["cubic_right_side_coefficient_of_zeta_4q"] == "-9/4"
    return {
        "status": "passed",
        "arithmetic": "Python standard-library Fraction; no floating point",
        "scope": "Finite diagnostics; the TeX contains the universal proof",
        "q_values": [1, 2, 3, 4],
        "maximum_anchor_power": 5,
        "cubic_polynomial_checks": len(cubic),
        "finite_anchor_checks": len(anchors),
        "cubic_cutoff_results": cubic,
        "finite_anchor_results": anchors,
        "euler_factors": euler_factors,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("even_tail_verification.json"))
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in
                      ("status", "cubic_polynomial_checks", "finite_anchor_checks",
                       "euler_factors")}, indent=2))


if __name__ == "__main__":
    main()
