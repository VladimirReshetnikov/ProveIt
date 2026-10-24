#!/usr/bin/env python3
"""Independent exact checks for residue-separated Diophantine root mergers.

Standard library only. No supplied builder is imported or executed. Symbolic
identities use a sparse polynomial implementation local to this file. Finite
checks are explicitly distinguished from the accompanying unbounded proof.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import isqrt
from pathlib import Path
import argparse
import hashlib
import json
import random


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Poly:
    """Integer polynomial in exactly four independent symbols."""

    def __init__(self, value=0):
        self.terms = dict(value) if isinstance(value, dict) else ({(0, 0, 0, 0): value} if value else {})
        self.terms = {k: v for k, v in self.terms.items() if v}

    @staticmethod
    def var(index):
        power = [0] * 4
        power[index] = 1
        return Poly({tuple(power): 1})

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Poly) else Poly(value)

    def __add__(self, other):
        other = self.coerce(other)
        result = self.terms.copy()
        for monomial, coefficient in other.terms.items():
            result[monomial] = result.get(monomial, 0) + coefficient
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        result = {}
        for p, a in self.terms.items():
            for q, b in other.terms.items():
                monomial = tuple(x + y for x, y in zip(p, q))
                result[monomial] = result.get(monomial, 0) + a * b
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, "bad exponent")
        result, base = Poly(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def digest(self):
        data = json.dumps([[list(k), v] for k, v in sorted(self.terms.items())], separators=(",", ":"))
        return hashlib.sha256(data.encode()).hexdigest()


def f8(x, a, b, c):
    return ((x * x - a - b - c) ** 2 - 4 * (a * b + a * c + b * c)) ** 2 - 64 * a * b * c * x * x


def primitive(t, a, delta, r):
    return (delta * (t * (t + 1) - a) - r) ** 2 - (4 * a + 1) * delta * r


def square_root(n):
    if n < 0:
        return None
    r = isqrt(n)
    return r if r * r == n else None


def multiquadratic_norm_value(x, radicands):
    """Norm via successive conjugation in a bitmask multiquadratic algebra.

    This routine does not use any pre-expanded source norm formula. Terms
    with mask m multiply with relation sqrt(d_j)^2=d_j. At each step the
    conjugation removes one independent formal square root.
    """
    value = {0: x, **{1 << j: -1 for j in range(len(radicands))}}
    for j in range(len(radicands)):
        conjugate = {m: -v if m & (1 << j) else v for m, v in value.items()}
        product_value = {}
        for a, u in value.items():
            for b, v in conjugate.items():
                scalar = u * v
                common = a & b
                for k, d in enumerate(radicands):
                    if common & (1 << k):
                        scalar *= d
                target = a ^ b
                product_value[target] = product_value.get(target, 0) + scalar
        value = {m: v for m, v in product_value.items() if v}
        require(not any(m & ((1 << (j + 1)) - 1) for m in value), "conjugation failed to remove a radical")
    require(set(value) <= {0}, "norm did not become scalar")
    return value.get(0, 0)


def symbolic_checks():
    x, u, v, w = [Poly.var(i) for i in range(4)]
    conjugates = Poly(1)
    for e1, e2, e3 in product((-1, 1), repeat=3):
        conjugates *= x - e1 * u - e2 * v - e3 * w
    displayed = f8(x, u * u, v * v, w * w)
    require(conjugates == displayed, "eight-conjugate identity")

    t, a, d, r = [Poly.var(i) for i in range(4)]
    carrier = 2 * t + 1
    first = 4 * a + 1
    raw = (d * (carrier * carrier + first) - 4 * r) ** 2 - 4 * first * carrier * carrier * d * d
    reduced = primitive(t, a, d, r)
    require(raw == 16 * reduced, "primitive norm identity")

    # Resultant via elimination of s^2+s=a. This is an independent form.
    numerator = d * (t * t + a) - r
    resultant = numerator * (numerator + d * carrier) - a * (d * carrier) ** 2
    require(reduced == resultant, "triangular-number resultant identity")

    # The literal three-root packet divides its raw norm by 256.
    t, a, B, c = [Poly.var(i) for i in range(4)]
    x, A = 2 * t + 1, 4 * a + 1
    U = t * (t + 1) - a - B + 4 * c
    M = U * U + 4 * x * x * c - A * B
    reduced_three = M * M - 16 * x * x * U * U * c
    require(f8(x, A, 4 * B, 16 * c) == 256 * reduced_three,
            "primitive three-root identity")

    # The literal centered pair shifts its carrier by the integer 2*z*k.
    t, z, k, unused = [Poly.var(i) for i in range(4)]
    H = t * (t + 1) + 4 * z * k * t + 2 * z * k - z * k * k
    shifted = t + 2 * z * k
    require(H == shifted * (shifted + 1) - z * (4 * z + 1) * k * k,
            "centered pair identity")

    # Parent first-row restoration and its actual native radicand.
    u, P, k, unused = [Poly.var(i) for i in range(4)]
    tau = 2 * u - 2 * P + k
    require(tau * tau + 2 * tau * (2 * P - k) + k * k - 4 ==
            4 * (u * u - 1 - P * (P - k)), "parent first-row restoration")
    X, Y, k, c = [Poly.var(i) for i in range(4)]
    eta = c - k * Y
    P = k + X * Y * (c - eta)
    require(1 + P * (P - k) == 1 + X * Y * Y * (X * Y * Y + 1) * k * k,
            "parent native first radicand")
    V, I, gap, unused = [Poly.var(i) for i in range(4)]
    require(V * V + (1 - I * I) * gap * (2 * V + gap) - 1 ==
            I * I * V * V - (I * I - 1) * (V + gap) ** 2 - 1,
            "parent auxiliary restoration")

    # n abbreviates the complete guard expression independent of p3.
    n, p, unused1, unused2 = [Poly.var(i) for i in range(4)]
    require(4 * n + 1 - (2 * p + 1) ** 2 == 4 * (n - p * (p + 1)),
            "guard restoration identity")
    return {
        "eight_conjugate_product": {"terms": len(displayed.terms), "sha256": displayed.digest()},
        "primitive_norm_equals_raw_divided_by_16": {"terms": len(reduced.terms), "sha256": reduced.digest()},
        "triangular_resultant": "exact identity",
        "guard_restoration": "exact identity",
        "primitive_three_root_norm": {"terms": len(reduced_three.terms), "sha256": reduced_three.digest()},
        "centered_pair_shift": "exact identity",
        "parent_first_and_auxiliary_restorations": "three exact identities",
    }


def finite_two_root_checks():
    checked = zeros = 0
    for a, d, r, t in product(range(-3, 14), range(-4, 5), range(-10, 25), range(-12, 13)):
        if d == 0:
            continue
        checked += 1
        if primitive(t, a, d, r):
            continue
        zeros += 1
        A, x = 4 * a + 1, 2 * t + 1
        tau = Fraction(d * (x * x + A) - 4 * r, 2 * x * d)
        y = (x - tau) / 2
        require(tau.denominator == 1 and y.denominator == 1, "two-root nonintegral recovery")
        require(tau * tau == A and d * y * y == r, "two-root failed recovery")
    converse = 0
    for tau, y, d in product(range(-19, 20, 2), range(-10, 11), range(-4, 5)):
        if d == 0:
            continue
        a, t, r = (tau * tau - 1) // 4, (tau + 2 * y - 1) // 2, d * y * y
        require(primitive(t, a, d, r) == 0, "two-root failed completeness")
        converse += 1
    return {"tested_assignments": checked, "zeros_reconstructed": zeros, "converse_witnesses": converse}


def finite_three_root_checks():
    checked = zeros = 0
    for A, B, R in product(range(-7, 34, 4), range(-7, 34, 4), range(-7, 28)):
        roots = [square_root(n) for n in (A, B, R)]
        expected = set()
        if None not in roots:
            expected = {e1 * roots[0] + 2 * e2 * roots[1] + 4 * e3 * roots[2]
                        for e1, e2, e3 in product((-1, 1), repeat=3)}
        for x in range(-33, 34, 2):
            checked += 1
            value = f8(x, A, 4 * B, 16 * R)
            require((value == 0) == (x in expected), "three-root classification mismatch")
            zeros += value == 0
    pell = squares = 0
    for I, V in product(range(-20, 21), range(-90, 91)):
        Q = I * I
        if Q == 1:
            continue
        d, r = Q - 1, Q * V * V - 1
        pell += 1
        z = square_root(d * r)
        if z is None:
            continue
        squares += 1
        y = Fraction(z, d)
        require(y.denominator == 1 and Q * V * V - d * y * y == 1, "rational Pell recovery")
    return {"tested_assignments": checked, "zeros_classified": zeros,
            "rational_pell_assignments": pell, "rational_pell_square_cases": squares}


def negative_controls():
    require(f8(1, 5, 5, 1) == 0, "unweighted control not a zero")
    require(square_root(5) is None, "unweighted control not irrational")
    # Without the second odd residue, the two imaginary roots cancel.
    A, B, Q, V, x = 1, -12, 4, 0, 1
    R = (Q - 1) * (Q * V * V - 1)
    require(f8(x, A, 4 * B, 16 * R) == 0 and square_root(B) is None,
            "missing second residue control")
    # If delta=0, the polynomial loses the auxiliary condition entirely.
    require(f8(3, 1, 4, 0) == 0 and 1 * 2 * 2 != 1, "delta-zero control")
    return {
        "unweighted_irrational_roots_can_cancel": {"x": 1, "radicands": [5, 5, 1]},
        "second_odd_residue_is_necessary": {"x": x, "A": A, "B": B, "Q": Q, "V": V, "R": R},
        "delta_zero_is_excluded": {"x": 3, "A": 1, "B": 1, "Q": 1, "V": 2},
    }


def five_root_checks():
    rng = random.Random(1888)
    comparisons = zero_count = 0
    for _ in range(512):
        odd_parts = [rng.choice((-7, -3, 1, 5, 9, 13, 17, 21, 25)) for _ in range(4)]
        last = rng.randrange(-9, 36)
        radicands = [d * (4 ** j) for j, d in enumerate(odd_parts)] + [256 * last]
        x = 2 * rng.randrange(-40, 41) + 1
        value = multiquadratic_norm_value(x, radicands)
        roots = [square_root(d) for d in radicands]
        expected = None not in roots and any(sum(e * r for e, r in zip(signs, roots)) == x
                                             for signs in product((-1, 1), repeat=5))
        require((value == 0) == expected, "five-root bounded classification")
        zero_count += value == 0
        comparisons += 1
    completions = 0
    for _ in range(64):
        roots = [(2 * rng.randrange(-8, 9) + 1) * (2 ** j) for j in range(4)]
        roots += [16 * rng.randrange(-8, 9)]
        radicands = [r * r for r in roots]
        signs = [rng.choice((-1, 1)) for _ in roots]
        x = sum(s * r for s, r in zip(signs, roots))
        require(x % 2 == 1 and multiquadratic_norm_value(x, radicands) == 0,
                "five-root constructive zero")
        x += 2
        direct = 1
        for s in product((-1, 1), repeat=5):
            direct *= x - sum(e * r for e, r in zip(s, roots))
        require(multiquadratic_norm_value(x, radicands) == direct, "five-root exact conjugate product")
        completions += 1
    # A repeated irrational square class becomes a false positive if two
    # nominal valuation levels are allowed to coincide.
    collapsed = [1, 20, 20, 64, 256]
    require(multiquadratic_norm_value(25, collapsed) == 0 and square_root(20) is None,
            "five-root collapsed valuation control")
    return {"exact_norm_algorithm": "successive conjugation in a 32-dimensional formal algebra",
            "bounded_classification_assignments": comparisons, "bounded_zeros": zero_count,
            "constructive_square_families": completions,
            "collapsed_valuation_counterexample": {"x": 25, "radicands": collapsed}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    result = {
        "status": "PASS",
        "scope": "Independent exact identities and finite adversarial checks; not a consistency search or a substitute for the unbounded mathematical proof.",
        "implementation": "Python standard library; no source builder or external algebra package executed",
        "symbolic": symbolic_checks(),
        "two_root_finite_checks": finite_two_root_checks(),
        "three_root_finite_checks": finite_three_root_checks(),
        "negative_controls": negative_controls(),
        "five_root_checks": five_root_checks(),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
