#!/usr/bin/env python3
"""Exact finite diagnostics for the dyadic spectral identity.

No floating point, trigonometric functions, symbolic algebra package, or
conjugate inverses are used.  A number in a height-h radical tower is stored
as 2**h rational coefficients.  The tower may have redundant extensions;
equality is therefore tested by the recursive sign algorithm, not merely by
comparing coefficient arrays.

This checks specified finite examples.  It is NOT a formal proof of the
universal polygon inequality or a verification of its provability in iPRA.

Usage:
    python3 code/dyadic_spectral_check.py
    python3 code/dyadic_spectral_check.py --max-n 4 --output checks.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import sys
from time import monotonic_ns


Number = tuple[Q, ...]
ComplexNumber = tuple[Number, Number]


def add(x: Number, y: Number) -> Number:
    assert len(x) == len(y)
    return tuple(a + b for a, b in zip(x, y))


def neg(x: Number) -> Number:
    return tuple(-a for a in x)


def sub(x: Number, y: Number) -> Number:
    return add(x, neg(y))


def scale(x: Number, q: Q | int) -> Number:
    return tuple(a * q for a in x)


def level(x: Number) -> int:
    n = len(x)
    assert n > 0 and n & (n - 1) == 0
    return n.bit_length() - 1


class RadicalTower:
    """Successive positive square roots of nonnegative earlier elements."""

    def __init__(self) -> None:
        self.radicands: list[Number] = []
        self.radicand_signs: list[int] = []

    @property
    def height(self) -> int:
        return len(self.radicands)

    def rational(self, q: Q | int, h: int | None = None) -> Number:
        h = self.height if h is None else h
        return (Q(q),) + (Q(0),) * ((1 << h) - 1)

    def promote(self, x: Number, h: int | None = None) -> Number:
        h = self.height if h is None else h
        assert level(x) <= h
        return x + (Q(0),) * ((1 << h) - len(x))

    def positive_root(self, d: Number) -> Number:
        assert level(d) == self.height
        sd = self.sign(d)
        assert sd >= 0, "Attempt to adjoin a root of a negative radicand"
        self.radicands.append(d)
        self.radicand_signs.append(sd)
        # The new generator has coefficient 1 in the upper half.
        n = len(d)
        return (Q(0),) * n + (Q(1),) + (Q(0),) * (n - 1)

    @lru_cache(maxsize=65536)
    def mul(self, x: Number, y: Number) -> Number:
        assert len(x) == len(y)
        h = level(x)
        if h == 0:
            return (x[0] * y[0],)
        if not any(x) or not any(y):
            return self.rational(0, h)
        n = len(x) // 2
        a, b = x[:n], x[n:]
        c, d = y[:n], y[n:]
        ac = self.mul(a, c)
        if not any(b) and not any(d):
            return ac + self.rational(0, h - 1)
        bd = self.mul(b, d)
        low = add(ac, self.mul(bd, self.radicands[h - 1]))
        high = add(self.mul(a, d), self.mul(b, c))
        return low + high

    def square(self, x: Number) -> Number:
        return self.mul(x, x)

    @lru_cache(maxsize=65536)
    def sign(self, x: Number) -> int:
        h = level(x)
        if h == 0:
            return (x[0] > 0) - (x[0] < 0)
        n = len(x) // 2
        a, b = x[:n], x[n:]
        sa = self.sign(a)
        if self.radicand_signs[h - 1] == 0:
            return sa
        sb = self.sign(b)
        if sa == 0:
            return sb
        if sb == 0 or sa == sb:
            return sa
        # For opposite signs, rationalize only the comparison, never an
        # inverse: sign(a+b*sqrt(d)) = sign(a)*sign(a*a-b*b*d).
        delta = sub(
            self.square(a),
            self.mul(self.square(b), self.radicands[h - 1]),
        )
        return sa * self.sign(delta)

    def cadd(self, z: ComplexNumber, w: ComplexNumber) -> ComplexNumber:
        return add(z[0], w[0]), add(z[1], w[1])

    def cmul(self, z: ComplexNumber, w: ComplexNumber) -> ComplexNumber:
        return (
            sub(self.mul(z[0], w[0]), self.mul(z[1], w[1])),
            add(self.mul(z[0], w[1]), self.mul(z[1], w[0])),
        )

    def cnorm2(self, z: ComplexNumber) -> Number:
        return add(self.square(z[0]), self.square(z[1]))

    def powers(self, z: ComplexNumber, count: int) -> list[ComplexNumber]:
        ans = [(self.rational(1), self.rational(0))]
        for _ in range(count):
            ans.append(self.cmul(ans[-1], z))
        return ans


def make_half_step(n: int) -> tuple[RadicalTower, ComplexNumber]:
    """Construct eta = exp(pi*i/n) by positive half-angle radicals."""
    assert n >= 4 and n & (n - 1) == 0
    tower = RadicalTower()
    a = tower.positive_root((Q(1, 2),))
    c, s = a, a  # cos(pi/4) = sin(pi/4) = positive sqrt(1/2).
    current = 4
    while current < n:
        old_c = c
        c = tower.positive_root(scale(add(tower.rational(1), old_c), Q(1, 2)))
        old_c = tower.promote(old_c)
        s = tower.positive_root(scale(sub(tower.rational(1), old_c), Q(1, 2)))
        c = tower.promote(c)
        current *= 2
    return tower, (c, s)


def rational_area_energy(vertices: list[tuple[Q, Q]]) -> tuple[Q, Q]:
    area2, energy = Q(0), Q(0)
    for p, q in zip(vertices, vertices[1:] + vertices[:1]):
        area2 += p[0] * q[1] - p[1] * q[0]
        energy += (q[0] - p[0]) ** 2 + (q[1] - p[1]) ** 2
    return area2 / 2, energy


def check_case(name: str, vertices: list[tuple[Q, Q]]) -> dict:
    n = len(vertices)
    started = monotonic_ns()
    tower, eta = make_half_step(n)
    one, zero = tower.rational(1), tower.rational(0)
    c, s = eta
    eta_powers = tower.powers(eta, 2 * n)
    assert tower.sign(sub(tower.cnorm2(eta), one)) == 0
    assert tower.sign(add(eta_powers[n][0], one)) == 0
    assert tower.sign(eta_powers[n][1]) == 0
    assert tower.sign(sub(eta_powers[2 * n][0], one)) == 0
    assert tower.sign(eta_powers[2 * n][1]) == 0
    upper_signs = [tower.sign(eta_powers[j][1]) for j in range(n + 1)]
    assert upper_signs == [0] + [1] * (n - 1) + [0]

    zeta_powers = [eta_powers[2 * j] for j in range(n)]
    orthogonality_checks = 0
    for k in range(1, n):
        total = (zero, zero)
        for j in range(n):
            total = tower.cadd(total, zeta_powers[(j * k) % n])
        assert tower.sign(total[0]) == tower.sign(total[1]) == 0
        orthogonality_checks += 1

    coefficients = []
    for k in range(n):
        coefficient = (zero, zero)
        for j, (x, y) in enumerate(vertices):
            z = (tower.rational(x), tower.rational(y))
            coefficient = tower.cadd(
                coefficient, tower.cmul(z, zeta_powers[(-j * k) % n])
            )
        coefficients.append(
            (scale(coefficient[0], Q(1, n)), scale(coefficient[1], Q(1, n)))
        )

    area, energy = rational_area_energy(vertices)
    lhs = sub(scale(c, energy), scale(s, 4 * area))
    rhs, reconstructed_energy, reconstructed_area = zero, zero, zero
    summand_signs = []
    for k, ak in enumerate(coefficients):
        ak_norm2 = tower.cnorm2(ak)
        xk, yk = eta_powers[k]
        reconstructed_energy = add(
            reconstructed_energy, scale(tower.mul(ak_norm2, tower.square(yk)), 4 * n)
        )
        reconstructed_area = add(
            reconstructed_area,
            scale(tower.mul(ak_norm2, tower.mul(xk, yk)), n),
        )
        if k:
            term = scale(
                tower.mul(ak_norm2, tower.mul(yk, eta_powers[k - 1][1])),
                4 * n,
            )
            term_sign = tower.sign(term)
            assert term_sign >= 0
            summand_signs.append(term_sign)
            rhs = add(rhs, term)

    assert tower.sign(sub(reconstructed_energy, tower.rational(energy))) == 0
    assert tower.sign(sub(reconstructed_area, tower.rational(area))) == 0
    difference_sign = tower.sign(sub(lhs, rhs))
    assert difference_sign == 0
    lhs_sign = tower.sign(lhs)
    assert lhs_sign >= 0
    energy_gap_sign = tower.sign(sub(tower.rational(energy), scale(s, 4 * abs(area))))
    assert energy_gap_sign >= 0

    return {
        "name": name,
        "N": n,
        "vertices": [[str(x), str(y)] for x, y in vertices],
        "signed_area": str(area),
        "energy": str(energy),
        "radical_tower_height": tower.height,
        "coefficient_array_length": 1 << tower.height,
        "root_of_unity_checks_passed": True,
        "upper_semicircle_signs": upper_signs,
        "orthogonality_checks_passed": orthogonality_checks,
        "energy_and_area_fourier_identities_passed": True,
        "spectral_identity_difference_sign": difference_sign,
        "spectral_lhs_sign": lhs_sign,
        "spectral_summand_signs": summand_signs,
        "E_minus_4s_absA_sign": energy_gap_sign,
        "elapsed_milliseconds": (monotonic_ns() - started) // 1_000_000,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, choices=(4, 8, 16), default=16)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[1] / "verification" / "dyadic_spectral_checks.json",
    )
    args = parser.parse_args()
    examples = [
        ("unit_diamond", [(Q(1), Q(0)), (Q(0), Q(1)), (Q(-1), Q(0)), (Q(0), Q(-1))]),
        ("rational_quadrilateral", [(Q(0), Q(0)), (Q(7, 3), Q(1, 5)), (Q(2), Q(5, 2)), (Q(-1, 4), Q(1))]),
        ("rational_octagon", [(Q((3 * j + 1) % 7 - 3, 2), Q((j * j + 2) % 11 - 5, 3)) for j in range(8)]),
        ("rational_hexadecagon", [(Q((3 * j + 1) % 7 - 3, 2), Q((j * j + 2) % 11 - 5, 3)) for j in range(16)]),
    ]
    results = [check_case(name, vertices) for name, vertices in examples if len(vertices) <= args.max_n]
    result = {
        "status": "all specified exact diagnostics passed",
        "scope": "Finite diagnostic examples, not a universal formal proof or an iPRA derivation.",
        "arithmetic": "fractions.Fraction; positive quadratic radical towers; recursive exact sign comparison",
        "floating_point_or_trigonometry_used": False,
        "identity": "c E - 4 s A = 4 N sum(k=1..N-1, |a_k|^2 Im(eta^k) Im(eta^(k-1)))",
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "python_version": sys.version.split()[0],
        "cases": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "cases": len(results), "output": str(args.output)}))


if __name__ == "__main__":
    main()
