#!/usr/bin/env python3
"""Exact finite-field checks for the norm-layer obstruction.

Standard-library only.  Enumerates every ratio theta in F_(q^p) for
(p,q)=(3,3),(5,5),(3,9), using separately checked irreducible moduli.
The constant-norm condition is evaluated directly at every j in F_p
and compared with the Frobenius condition.  This verifies finite examples;
the general assertions are proved in the accompanying manuscript.
"""

import argparse
import itertools
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def polynomial_remainder(a, b, p):
    a = list(a)
    while len(a) >= len(b):
        lead = a[-1]
        shift = len(a) - len(b)
        if lead:
            for j, coefficient in enumerate(b):
                a[j + shift] = (a[j + shift] - lead * coefficient) % p
        while a and a[-1] == 0:
            a.pop()
    return a


def check_irreducible(modulus, p):
    """Every reducible degree-n polynomial has a factor of degree <=n/2."""
    n = len(modulus) - 1
    require(modulus[-1] == 1, "The modulus must be monic")
    checked = 0
    for degree in range(1, n // 2 + 1):
        for coefficients in itertools.product(range(p), repeat=degree):
            divisor = list(coefficients) + [1]
            checked += 1
            require(polynomial_remainder(modulus, divisor, p),
                    f"Reducible modulus: factor {divisor}")
    return checked


class FiniteField:
    def __init__(self, p, modulus):
        self.p = p
        self.modulus = list(modulus)
        self.degree = len(modulus) - 1
        self.size = p ** self.degree
        self.powers = [p ** j for j in range(self.degree)]
        self.coefficients = [
            tuple(x // power % p for power in self.powers)
            for x in range(self.size)
        ]

    def encode(self, coefficients):
        return sum(c % self.p * power
                   for c, power in zip(coefficients, self.powers))

    def add(self, x, y):
        return self.encode(a + b for a, b in
                           zip(self.coefficients[x], self.coefficients[y]))

    def subtract(self, x, y):
        return self.encode(a - b for a, b in
                           zip(self.coefficients[x], self.coefficients[y]))

    def multiply(self, x, y):
        p, n = self.p, self.degree
        coefficients = [0] * (2 * n - 1)
        for i, a in enumerate(self.coefficients[x]):
            for j, b in enumerate(self.coefficients[y]):
                coefficients[i + j] += a * b
        for i in range(2 * n - 2, n - 1, -1):
            lead = coefficients[i]
            for j, c in enumerate(self.modulus[:-1]):
                coefficients[i - n + j] -= lead * c
        return self.encode(coefficients[:n])

    def power(self, x, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = self.multiply(result, x)
            x = self.multiply(x, x)
            exponent //= 2
        return result


def check_case(p, q, modulus):
    factor_checks = check_irreducible(modulus, p)
    field = FiniteField(p, modulus)
    require(field.size == q ** p, "Incorrect extension degree")
    exponent = (field.size - 1) // (q - 1)
    norms = [field.power(x, exponent) for x in range(field.size)]
    require(all(field.power(x, q) == x for x in norms),
            "A computed norm is outside F_q")
    constant_ratios, frobenius_ratios = [], []
    for theta in range(field.size):
        # j is embedded in the prime field by its constant coefficient.
        if len({norms[field.add(theta, j)] for j in range(p)}) == 1:
            constant_ratios.append(theta)
        difference = field.subtract(field.power(theta, q), theta)
        if 0 < difference < p:
            frobenius_ratios.append(theta)
    require(constant_ratios == frobenius_ratios,
            "The two independently computed ratio sets disagree")
    require(len(constant_ratios) == q * (p - 1),
            "Unexpected exact ratio count")
    require(0 not in constant_ratios, "Zero cannot be a constant ratio")

    # Exhaustive direct start-direction counting in the smallest example.
    direct_count = None
    if field.size == 27:
        direct_count = 0
        for a in range(field.size):
            local = 0
            for h in range(1, field.size):
                values = {norms[field.add(a, field.multiply(j, h))]
                          for j in range(p)}
                local += len(values) == 1
            require(local == (q * (p - 1) if a else 0),
                    "Unexpected direct fixed-start count")
            direct_count += local
        require(direct_count == (field.size - 1) * q * (p - 1),
                "Unexpected direct total count")
    return {
        "characteristic": p,
        "base_field_size": q,
        "extension_field_size": field.size,
        "prime_field_modulus_coefficients_ascending": list(modulus),
        "monic_divisors_excluded": factor_checks,
        "all_extension_elements_checked": field.size,
        "constant_norm_ratios": len(constant_ratios),
        "frobenius_ratio_set_matches": True,
        "ordered_full_p_constant_progressions":
            (field.size - 1) * len(constant_ratios),
        "independent_direct_pair_count": direct_count,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    cases = [
        check_case(3, 3, [2, 2, 0, 1]),
        check_case(5, 5, [4, 4, 0, 0, 0, 1]),
        check_case(3, 9, [2, 1, 0, 0, 0, 0, 1]),
    ]
    lower_bound = 5 ** 3 * (5 ** 5 - 1) * 5 * (5 - 1)
    require(lower_bound == 7810000, "Arithmetic error in layered example")
    report = {
        "status": "all exact checks passed",
        "arithmetic": "Python integers and finite-field modular arithmetic",
        "cases": cases,
        "norm3_plus_norm5_over_F5_dimension8": {
            "nonzero_quintic_block_centers": 5 ** 3 * (5 ** 5 - 1),
            "certified_nonzero_directions_at_each_such_center": 20,
            "symmetric_four_term_progression_lower_bound": lower_bound,
            "claim_type": "lower bound, not an exact symmetric-pattern count",
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
