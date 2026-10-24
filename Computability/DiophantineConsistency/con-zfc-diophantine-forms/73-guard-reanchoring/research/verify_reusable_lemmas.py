#!/usr/bin/env python3
"""Finite, exact checks accompanying reusable_lemmas.tex.

Python 3.10+, standard library only. No checks depend on assert, and running
with python -O preserves every check. The unbounded statements are proved in
the TeX section; this script does not establish a consistency equivalence.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from functools import lru_cache
from itertools import product
import json
from math import isqrt
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def J(a, b):
    return (a + b) ** 2 + a + 1


def U(a, b):
    return 4 * J(a, b)


def C(a, b):
    return U(a, b) + 1


def N(a):
    return 4 * a + 2


def V(a):
    return 4 * a + 3


EPSILON = ("epsilon",)
IOTA = ("iota",)


def unpair(value):
    """Return the inverse of J, or None when value is not in its image."""
    if value < 1:
        return None
    total = isqrt(value - 1)
    first = value - total * total - 1
    if first > total:
        return None
    return first, total - first


@lru_cache(maxsize=None)
def decode(value):
    require(isinstance(value, int) and value >= 0, "Natural code required")
    if value == 0:
        return EPSILON
    if value == 1:
        return IOTA
    tag = value % 4
    if tag == 2:
        return ("N", decode((value - 2) // 4))
    if tag == 3:
        return ("V", decode((value - 3) // 4))
    children = unpair(value // 4)
    if children is None:
        return ("extra", value)
    left, right = children
    require(left < value and right < value, "Nondecreasing binary decoding")
    return ("U" if tag == 0 else "C", decode(left), decode(right))


def encode(term):
    tag = term[0]
    if tag == "epsilon":
        return 0
    if tag == "iota":
        return 1
    if tag == "extra":
        return term[1]
    if tag in ("U", "C"):
        constructor = U if tag == "U" else C
        return constructor(encode(term[1]), encode(term[2]))
    require(tag in ("N", "V"), "Unknown term symbol")
    return (N if tag == "N" else V)(encode(term[1]))


def retract(term):
    if term[0] == "extra":
        return EPSILON
    return (term[0],) + tuple(retract(t) for t in term[1:])


def retract_code(value):
    return encode(retract(decode(value)))


def local_polynomial(a, b, c, d, e, f, z):
    reflexive = (a - b) ** 2
    transversal = (c - e) ** 2 + (a - d) ** 2 + (b - f) ** 2
    binary = (a - U(c, e) - z) ** 2 + (b - U(d, f) - z) ** 2
    unary = (a - 4 * c - 2 - z) ** 2 + (b - 4 * d - 2 - z) ** 2
    return z**2 * (z - 1) ** 2 + reflexive * transversal * binary * unary


def structural_rule(a, b, c, d, e, f, z):
    """Independent rule recognition on decoded trees, rather than residuals."""
    if z not in (0, 1):
        return False
    ta, tb, tc, td, te, tf = map(decode, (a, b, c, d, e, f))
    binary_tag = "U" if z == 0 else "C"
    unary_tag = "N" if z == 0 else "V"
    return (
        ta == tb
        or (tc == te and ta == td and tb == tf)
        or (ta == (binary_tag, tc, te) and tb == (binary_tag, td, tf))
        or (ta == (unary_tag, tc) and tb == (unary_tag, td))
    )


class Poly:
    """Small exact univariate polynomials for the degree certificate."""

    def __init__(self, coeffs):
        self.coeffs = list(coeffs)
        while len(self.coeffs) > 1 and self.coeffs[-1] == 0:
            self.coeffs.pop()

    @staticmethod
    def convert(value):
        return value if isinstance(value, Poly) else Poly([value])

    def __add__(self, other):
        other = self.convert(other)
        size = max(len(self.coeffs), len(other.coeffs))
        values = [0] * size
        for i, value in enumerate(self.coeffs):
            values[i] += value
        for i, value in enumerate(other.coeffs):
            values[i] += value
        return Poly(values)

    __radd__ = __add__

    def __neg__(self):
        return Poly([-value for value in self.coeffs])

    def __sub__(self, other):
        return self + (-self.convert(other))

    def __rsub__(self, other):
        return self.convert(other) + (-self)

    def __mul__(self, other):
        other = self.convert(other)
        values = [0] * (len(self.coeffs) + len(other.coeffs) - 1)
        for i, left in enumerate(self.coeffs):
            for j, right in enumerate(other.coeffs):
                values[i + j] += left * right
        return Poly(values)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, "Invalid exponent")
        value, factor = Poly([1]), self
        while exponent:
            if exponent % 2:
                value = value * factor
            exponent //= 2
            if exponent:
                factor = factor * factor
        return value


def check_syntax():
    pairs = {}
    constructor_checks = 0
    for a, b in product(range(80), repeat=2):
        paired = J(a, b)
        require(paired not in pairs, "Pairing collision")
        require(paired > max(a, b), "Pairing does not increase")
        require(unpair(paired) == (a, b), "Pairing inverse mismatch")
        pairs[paired] = (a, b)
        for tag, function in (("U", U), ("C", C)):
            value = function(a, b)
            require(value > max(a, b), "Constructor does not increase")
            require(decode(value) == (tag, decode(a), decode(b)), "Decode mismatch")
            require(
                retract_code(value) == function(retract_code(a), retract_code(b)),
                "Binary retraction is not a homomorphism",
            )
            constructor_checks += 1
    for value in range(8192):
        require(encode(decode(value)) == value, "Extended-code round trip failed")
        for tag, function in (("N", N), ("V", V)):
            require(
                decode(function(value)) == (tag, decode(value)),
                "Unary decoding mismatch",
            )
            require(
                retract_code(function(value)) == function(retract_code(value)),
                "Unary retraction is not a homomorphism",
            )
            constructor_checks += 1
    require(decode(16) == ("extra", 16), "Expected unused original code")
    require(retract_code(16) == 0, "Extra constant was not retracted")

    local_checks = 0
    for ports in product(range(4), repeat=6):
        for z in (-1, 0, 1, 2):
            require(
                (local_polynomial(*ports, z) == 0) == structural_rule(*ports, z),
                "Polynomial and structural rule recognition disagree",
            )
            local_checks += 1
    # Exercise binary constructors whose result codes lie above the small box.
    for c, d, e, f in product(range(4), repeat=4):
        for z, binary, unary in ((0, U, N), (1, C, V)):
            for a, b in ((binary(c, e), binary(d, f)), (unary(c), unary(d))):
                require(local_polynomial(a, b, c, d, e, f, z) == 0, "Valid rule rejected")
                require(structural_rule(a, b, c, d, e, f, z), "Structural oracle failed")
                local_checks += 1
    # A product-only formula would incorrectly accept z=2 at reflexive lines.
    require(local_polynomial(0, 0, 0, 0, 0, 0, 2) != 0, "Binary guard missing")
    require(
        local_polynomial(U(0, 0), U(1, 1), 0, 1, 0, 1, 1) != 0,
        "Wrong constructor tag accepted",
    )

    t = Poly([0, 1])
    specialization = local_polynomial(t, 0, t, 0, 0, 0, 0)
    independent = 2 * t**4 * ((4 * t**2 + 3 * t + 4) ** 2 + 16) * ((3 * t + 2) ** 2 + 4)
    require(specialization.coeffs == independent.coeffs, "Degree identity failed")
    require(len(specialization.coeffs) == 11, "Wrong specialization degree")
    require(specialization.coeffs[-1] == 288, "Wrong leading coefficient")
    return {
        "pairing_pairs": len(pairs),
        "round_trip_codes": 8192,
        "constructor_and_retraction_checks": constructor_checks,
        "local_rule_checks": local_checks,
        "local_degree": 10,
        "degree_specialization_leading_coefficient": 288,
        "negative_controls": ["z=2 rejected", "wrong constructor tag rejected"],
    }


def validate_certificate(lines):
    require(lines and lines[0] == {"equation": [0, 0], "kind": "seed"}, "Missing valid seed")
    for index, line in enumerate(lines[1:], 1):
        a, b = line["equation"]
        if line["kind"] == "axiom":
            value = line["substitution"]
            # Fixed theory: U(x,epsilon)=iota and U(x,epsilon)=V(epsilon).
            right = 1 if line["axiom"] == 0 else V(0)
            require(line["axiom"] in (0, 1), "Unknown axiom")
            require([a, b] == [U(value, 0), right], "Incorrect axiom instance")
        else:
            require(line["kind"] == "inference", "Unknown justification")
            first, second = line["premises"]
            require(0 <= first < index and 0 <= second < index, "Circular or missing premise")
            c, d = lines[first]["equation"]
            e, f = lines[second]["equation"]
            require(local_polynomial(a, b, c, d, e, f, line["z"]) == 0, "Invalid inference")


def check_certificate_retraction():
    # The unused code 16 occurs in an intermediate term, but the conclusion is closed.
    lines = [
        {"equation": [0, 0], "kind": "seed"},
        {"equation": [U(16, 0), 1], "kind": "axiom", "axiom": 0, "substitution": 16},
        {"equation": [U(16, 0), V(0)], "kind": "axiom", "axiom": 1, "substitution": 16},
        {"equation": [1, V(0)], "kind": "inference", "premises": [1, 2], "z": 0},
    ]
    validate_certificate(lines)
    transformed = deepcopy(lines)
    for line in transformed:
        line["equation"] = [retract_code(value) for value in line["equation"]]
        if "substitution" in line:
            line["substitution"] = retract_code(line["substitution"])
    validate_certificate(transformed)
    require(transformed[-1]["equation"] == lines[-1]["equation"], "Closed target changed")
    corrupted = deepcopy(lines)
    corrupted[-1]["premises"][0] = len(lines) - 1
    try:
        validate_certificate(corrupted)
    except ValueError:
        pass
    else:
        raise ValueError("Circular proof negative control accepted")
    return {"original_lines": len(lines), "retracted_lines": len(transformed), "closed_target": [1, 3], "circular_proof_rejected": True}


def pell(base, index):
    chi, psi = 1, 0
    delta = base * base - 1
    for _ in range(index):
        chi, psi = base * chi + delta * psi, chi + base * psi
    return chi, psi


def check_pell():
    bound_checks = 0
    for base in range(2, 15):
        for index in range(1, 31):
            chi, psi = pell(base, index)
            require((2 * base - 1) ** (index - 1) <= psi <= (2 * base) ** (index - 1), "Pell bound failed")
            require(chi * chi - (base * base - 1) * psi * psi == 1, "Pell norm failed")
            bound_checks += 1
    quotient_checks = 0
    for a in range(1, 33):
        base, modulus = a + 2, 4 * a + 3
        for index in range(25):
            chi, psi = pell(base, index)
            quotient = sum(2 ** (index - 1 - j) * pell(base, j)[1] for j in range(index))
            require(chi - a * psi == 2**index + modulus * quotient, "Exact Pell quotient failed")
            quotient_checks += 1
    # A negative main root does not obey the claimed positive-root congruence.
    a, rank = 2, 3
    chi, psi = pell(a + 2, rank)
    require((-chi - a * psi - 2**rank) % (4 * a + 3) != 0, "Sign negative control inconclusive")

    ratio_cases = 0
    complete_hypothesis_cases = 0
    for X in range(1, 65):
        for n in range(2, 5):
            rank = 2 * n - 1
            limit_floor = (X + 1) ** (rank - 1) // (2 * X ** (n - 1))
            for Y in range(max(1, limit_floor - 5), limit_floor + 7):
                a, first_base = (X + 1) * Y, 2 * X * Y * Y + 1
                D, c = pell(a + 2, rank)
                k = 2 * pell(first_base, n)[1]
                if not k * Y < c < k * (Y + 1):
                    continue
                ratio_cases += 1
                H = 4 * a + 3
                require(c > k * 2 ** (rank - 2), "Power ratio inequality failed")
                require(Y >= 2 ** (rank - 2), "Integral Y bound failed")
                require(0 < X < H and 0 < 2**rank < H, "Congruence interval failed")
                if (D - a * c - X) % H == 0:
                    require(X == 2**rank, "Power recovery failed")
                    complete_hypothesis_cases += 1
    require(complete_hypothesis_cases >= 2, "Expected nonvacuous power examples missing")
    return {
        "recurrence_bound_and_norm_checks": bound_checks,
        "exact_quotient_checks": quotient_checks,
        "strict_ratio_cases": ratio_cases,
        "all_power_hypotheses_cases": complete_hypothesis_cases,
        "negative_root_control_rejected": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON receipt path")
    args = parser.parse_args()
    receipt = {
        "status": "PASS",
        "scope": "finite exact checks; unrestricted results are proved in reusable_lemmas.tex",
        "syntax": check_syntax(),
        "certificate_retraction": check_certificate_retraction(),
        "pell": check_pell(),
    }
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
