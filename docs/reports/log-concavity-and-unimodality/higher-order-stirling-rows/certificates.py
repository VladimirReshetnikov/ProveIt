#!/usr/bin/env python3
"""Check all polynomial certificates using only exact rational arithmetic.

No computer algebra package is required. Polynomials are coefficient tuples in
ascending order. Every identity is verified by coefficient equality, not by
sampling numerical arguments. The output records the actual certificates.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
from typing import Tuple, Any, List, Dict


@dataclass(frozen=True)
class Poly:
    coefficients: Tuple[Fraction, ...]

    def __init__(self, values: Any = 0):
        if isinstance(values, Poly):
            coefficients = values.coefficients
        elif isinstance(values, (int, Fraction)):
            coefficients = (Fraction(values),)
        else:
            coefficients = tuple(Fraction(v) for v in values)
        coefficients = coefficients or (Fraction(0),)
        while len(coefficients) > 1 and coefficients[-1] == 0:
            coefficients = coefficients[:-1]
        object.__setattr__(self, "coefficients", coefficients)

    def __add__(self, other: Any) -> Poly:
        b = Poly(other).coefficients
        a = self.coefficients
        return Poly([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                     for i in range(max(len(a), len(b)))])

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly([-v for v in self.coefficients])

    def __sub__(self, other: Any) -> Poly:
        return self + (-Poly(other))

    def __rsub__(self, other: Any) -> Poly:
        return Poly(other) - self

    def __mul__(self, other: Any) -> Poly:
        b = Poly(other).coefficients
        a = self.coefficients
        result = [Fraction(0)] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                result[i+j] += x*y
        return Poly(result)

    __rmul__ = __mul__

    def __truediv__(self, scalar: Any) -> Poly:
        return Poly([x / Fraction(scalar) for x in self.coefficients])

    def __pow__(self, exponent: int) -> Poly:
        if exponent < 0:
            raise ValueError("polynomial exponent must be nonnegative")
        answer, base = Poly(1), self
        while exponent:
            if exponent & 1:
                answer = answer * base
            base = base * base
            exponent >>= 1
        return answer

    def at(self, value: Any) -> Poly:
        value = Poly(value)
        result = Poly(0)
        for coefficient in reversed(self.coefficients):
            result = result * value + coefficient
        return result

    def text_coefficients(self) -> List[str]:
        return [str(v) for v in self.coefficients]


def falling_poly(t: Poly, d: int) -> Poly:
    result = Poly(1)
    for j in range(d):
        result = result * (t-j)
    return result


def verify_all() -> Dict[str, Any]:
    t = Poly([0, 1])
    records: List[Dict[str, Any]] = []

    def equal(name: str, lhs: Poly, rhs: Any) -> None:
        rhs = Poly(rhs)
        if lhs != rhs:
            raise AssertionError(f"polynomial identity failed: {name}")
        records.append({"name": name, "type": "coefficient identity",
                        "coefficients_ascending": lhs.text_coefficients(), "status": "passed"})

    def positive(name: str, expression: Poly, shift: int) -> None:
        shifted = expression.at(t + shift)
        if not all(v >= 0 for v in shifted.coefficients) or shifted.coefficients[0] <= 0:
            raise AssertionError(f"positive-coefficient certificate failed: {name}")
        records.append({"name": name, "type": "positive shifted coefficients",
                        "shift": shift, "coefficients_ascending": shifted.text_coefficients(),
                        "status": "passed"})

    expected_A = {
        0: Poly(0),
        1: Poly(1),
        2: 4*(2*t**2 - 2*t - 3),
        3: 9*(3*t**4 - 12*t**3 - 9*t**2 + 42*t + 40),
        4: 32*(2*t**6 - 18*t**5 + 17*t**4 + 168*t**3 - 55*t**2 - 834*t - 630),
    }
    expected_L = {
        0: Poly(0),
        1: Poly(2),
        2: 4*(4*t - 3)/3,
        3: 3*(3*t**2 - 15*t + 44)/2,
        4: -16*(2*t**3 + 9*t**2 - 161*t + 255)/5,
    }
    # C_d(t,k) = expected_C0[d] + k * expected_C1[d].
    expected_C0 = {
        0: Poly(0), 1: Poly(2), 2: 4*(2*t-1),
        3: 6*(3*t**2 - 6*t + 11),
        4: 16*(2*t**3 - 9*t**2 + 43*t - 51),
    }
    expected_C1 = {
        0: Poly(0), 1: Poly(0), 2: Poly(-8),
        3: 6*(-9*t+9), 4: 16*(-12*t**2 + 36*t - 54),
    }
    expected_M = {
        0: Poly(0), 1: Poly(2), 2: 8*(t-1),
        3: -18*(3*t-11), 4: -32*(t-2)*(2*t**2+4*t-51),
    }
    As, Ls, Ms = {}, {}, {}
    for d in range(5):
        P = falling_poly(t, d)
        minus, plus = P.at(t-d), P.at(t+d)
        A = P**2 - minus*plus
        C0, C1 = plus-minus, 2*P-minus-plus
        L = C0 + C1*t/(d+1)
        M = 2*t*P - (t+d)*minus - (t-d)*plus
        equal(f"A_{d}", A, expected_A[d])
        equal(f"C_{d}: constant in k", C0, expected_C0[d])
        equal(f"C_{d}: coefficient of k", C1, expected_C1[d])
        equal(f"L_{d}", L, expected_L[d])
        equal(f"M_{d}", M, expected_M[d])
        if d >= 1:
            positive(f"A_{d}>0 in the triangular interior", A, 2*(d+1))
        if 1 <= d <= 3:
            positive(f"L_{d}>0 in the triangular interior", L, 2*(d+1))
        if d >= 2:
            positive(f"centered second difference P_{d} is positive", -C1, 2*(d+1))
        As[d], Ls[d], Ms[d] = A, L, M

    E4 = 4*As[4] - Ls[4]**2
    E4_factored = Fraction(384, 25)*(t-5)*(2*t**2-6*t+9)*(7*t**3-31*t**2-126*t+1080)
    equal("subset order five discriminant factorization", E4, E4_factored)
    equal("expanded main discriminant, multiplied by 25", 25*E4,
          5376*t**6-66816*t**5+198528*t**4+1018368*t**3
          -7986816*t**2+18351360*t-18662400)
    equal("cubic at t=10+s", (7*t**3-31*t**2-126*t+1080).at(t+10),
          7*t**3+179*t**2+1354*t+3720)
    positive("subset order five discriminant positive", E4, 10)
    equal("cycle order four discriminant factorization", 36*As[3]-Ms[3]**2,
          972*(t-3)**2*(t-1)*(t+3))
    equal("cycle order five obstruction factorization", 64*As[4]-Ms[4]**2,
          -9216*(t-4)*(t+4)*(2*t-9)*(2*t**2-6*t+9))
    positive("negative cycle order five discriminant", Ms[4]**2-64*As[4], 10)

    # Here the polynomial variable is r, rather than t.
    numerator = 4*(t+1)**2*(2*t+3)**2
    denominator = 3*(t+2)**2*(3*t+2)*(3*t+1)
    gap = 11*t**4+55*t**3+74*t**2+12*t-12
    equal("successive row-three ratio denominator minus numerator", denominator-numerator, gap)
    equal("row-three ratio positive shift", gap.at(t+1),
          11*t**4+99*t**3+305*t**2+369*t+140)
    positive("row-three ratio decreases for all r>=1", gap, 1)

    # Leading terms used in the asymptotic diagnostic, for d=1..8.
    asymptotics = []
    for d in range(1, 9):
        P = falling_poly(t, d)
        minus, plus = P.at(t-d), P.at(t+d)
        A = P**2 - minus*plus
        C0, C1 = plus-minus, 2*P-minus-plus
        L = C0 + C1*t/(d+1)
        M = 2*t*P-(t+d)*minus-(t-d)*plus
        def coefficient(poly: Poly, index: int) -> Fraction:
            return poly.coefficients[index] if index < len(poly.coefficients) else Fraction(0)
        if coefficient(A, 2*d-2) != d**3:
            raise AssertionError("leading coefficient of A")
        if coefficient(L, d-1) != Fraction(d*d*(-d*d+3*d+2), d+1):
            raise AssertionError("leading coefficient of L")
        if coefficient(M, d-1) != d**3*(3-d):
            raise AssertionError("leading coefficient of M")
        asymptotics.append({"d": d, "A_leading": str(coefficient(A, 2*d-2)),
                            "L_leading": str(coefficient(L, d-1)),
                            "M_at_degree_d_minus_one": str(coefficient(M, d-1))})
    return {"arithmetic": "fraction-based polynomial ring over Q, standard library only",
            "identity_and_positivity_checks": len(records), "checks": records,
            "leading_coefficient_checks": asymptotics, "status": "passed"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/certificates.json"))
    args = parser.parse_args()
    report = verify_all()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {report['identity_and_positivity_checks']} polynomial identities/positivity certificates")
    print("PASS: 24 leading-coefficient checks (d=1,...,8)")
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
