#!/usr/bin/env python3
"""Exact constructive algebra certificates for trigonometric identities.

No numerical trigonometry is used.  Angles are interpreted in the Laurent
polynomial group algebra by

    cis(a+b) = cis(a) cis(b),   cis(pi/2) = i,
    cos a = (cis a + cis(-a))/2,
    sin a = (cis a - cis(-a))/(2i).

Every check is therefore finite arithmetic in Q(i)[z_1^±1,...,z_m^±1].
Rational identities are compared after exact cross multiplication.  This is
precisely the algebraic layer that the accompanying report lowers to iPRA.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
from typing import Any, Iterable
import json


# ---------- Gaussian rationals ----------

@dataclass(frozen=True)
class GQ:
    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    @staticmethod
    def coerce(x: Any) -> "GQ":
        if isinstance(x, GQ):
            return x
        if isinstance(x, Fraction):
            return GQ(x, Fraction(0))
        if isinstance(x, int):
            return GQ(Fraction(x), Fraction(0))
        raise TypeError(f"cannot coerce {type(x)} to GQ")

    def __add__(self, other: Any) -> "GQ":
        o = GQ.coerce(other)
        return GQ(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __neg__(self) -> "GQ":
        return GQ(-self.re, -self.im)

    def __sub__(self, other: Any) -> "GQ":
        return self + (-GQ.coerce(other))

    def __rsub__(self, other: Any) -> "GQ":
        return GQ.coerce(other) - self

    def __mul__(self, other: Any) -> "GQ":
        o = GQ.coerce(other)
        return GQ(self.re * o.re - self.im * o.im,
                  self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def inv(self) -> "GQ":
        d = self.re * self.re + self.im * self.im
        if d == 0:
            raise ZeroDivisionError("zero Gaussian rational")
        return GQ(self.re / d, -self.im / d)

    def __truediv__(self, other: Any) -> "GQ":
        return self * GQ.coerce(other).inv()

    def __pow__(self, n: int) -> "GQ":
        if n < 0:
            return (self.inv()) ** (-n)
        out = GQ(1)
        b = self
        k = n
        while k:
            if k & 1:
                out = out * b
            b = b * b
            k >>= 1
        return out

    def is_zero(self) -> bool:
        return self.re == 0 and self.im == 0

    def text(self) -> str:
        if self.im == 0:
            return str(self.re)
        if self.re == 0:
            return f"{self.im}*i"
        sign = "+" if self.im >= 0 else "-"
        return f"{self.re}{sign}{abs(self.im)}*i"


I = GQ(Fraction(0), Fraction(1))


# ---------- Laurent polynomials ----------

Monomial = tuple[tuple[str, int], ...]


def monomial_mul(a: Monomial, b: Monomial) -> Monomial:
    d: dict[str, int] = dict(a)
    for k, v in b:
        d[k] = d.get(k, 0) + v
        if d[k] == 0:
            del d[k]
    return tuple(sorted(d.items()))


@dataclass(frozen=True)
class LP:
    terms: tuple[tuple[Monomial, GQ], ...] = ()

    @staticmethod
    def from_dict(d: dict[Monomial, GQ]) -> "LP":
        clean = [(m, c) for m, c in d.items() if not c.is_zero()]
        clean.sort(key=lambda mc: mc[0])
        return LP(tuple(clean))

    @staticmethod
    def const(x: Any) -> "LP":
        c = GQ.coerce(x)
        return LP() if c.is_zero() else LP((((), c),))

    @staticmethod
    def var(name: str, exponent: int = 1) -> "LP":
        if exponent == 0:
            return LP.const(1)
        return LP.from_dict({((name, exponent),): GQ(1)})

    @staticmethod
    def coerce(x: Any) -> "LP":
        if isinstance(x, LP):
            return x
        if isinstance(x, (int, Fraction, GQ)):
            return LP.const(x)
        raise TypeError(f"cannot coerce {type(x)} to LP")

    def as_dict(self) -> dict[Monomial, GQ]:
        return dict(self.terms)

    def __add__(self, other: Any) -> "LP":
        o = LP.coerce(other)
        d = self.as_dict()
        for m, c in o.terms:
            d[m] = d.get(m, GQ()) + c
        return LP.from_dict(d)

    __radd__ = __add__

    def __neg__(self) -> "LP":
        return LP(tuple((m, -c) for m, c in self.terms))

    def __sub__(self, other: Any) -> "LP":
        return self + (-LP.coerce(other))

    def __rsub__(self, other: Any) -> "LP":
        return LP.coerce(other) - self

    def __mul__(self, other: Any) -> "LP":
        o = LP.coerce(other)
        if not self.terms or not o.terms:
            return LP()
        d: dict[Monomial, GQ] = {}
        for m1, c1 in self.terms:
            for m2, c2 in o.terms:
                m = monomial_mul(m1, m2)
                d[m] = d.get(m, GQ()) + c1 * c2
        return LP.from_dict(d)

    __rmul__ = __mul__

    def scale(self, c: Any) -> "LP":
        cc = GQ.coerce(c)
        if cc.is_zero():
            return LP()
        return LP(tuple((m, cc * a) for m, a in self.terms))

    def __truediv__(self, other: Any) -> "RF":
        return RF(self, LP.coerce(other))

    def __pow__(self, n: int) -> "LP":
        if n < 0:
            raise ValueError("negative LP powers belong to RF")
        out = LP.const(1)
        b = self
        k = n
        while k:
            if k & 1:
                out = out * b
            b = b * b
            k >>= 1
        return out

    def is_zero(self) -> bool:
        return not self.terms

    def is_constant(self) -> bool:
        return not self.terms or (len(self.terms) == 1 and self.terms[0][0] == ())

    def constant(self) -> GQ:
        if self.is_zero():
            return GQ()
        if not self.is_constant():
            raise ValueError("not constant")
        return self.terms[0][1]

    def divide_constant(self, c: GQ) -> "LP":
        return self.scale(c.inv())

    def text(self, max_terms: int = 8) -> str:
        if self.is_zero():
            return "0"
        pieces = []
        for idx, (m, c) in enumerate(self.terms):
            if idx >= max_terms:
                pieces.append(f"... ({len(self.terms)} terms)")
                break
            mon = "*".join(f"{v}^{e}" if e != 1 else v for v, e in m) or "1"
            pieces.append(f"({c.text()})*{mon}")
        return " + ".join(pieces)


# ---------- Rational functions over Laurent polynomials ----------

@dataclass(frozen=True)
class RF:
    num: LP
    den: LP = LP((((), GQ(1)),))

    def __post_init__(self) -> None:
        if self.den.is_zero():
            raise ZeroDivisionError("zero polynomial denominator")
        # Absorb constant denominators to keep polynomial identities compact.
        if self.den.is_constant():
            c = self.den.constant()
            object.__setattr__(self, "num", self.num.divide_constant(c))
            object.__setattr__(self, "den", LP.const(1))

    @staticmethod
    def coerce(x: Any) -> "RF":
        if isinstance(x, RF):
            return x
        if isinstance(x, LP):
            return RF(x)
        if isinstance(x, (int, Fraction, GQ)):
            return RF(LP.const(x))
        raise TypeError(f"cannot coerce {type(x)} to RF")

    def __add__(self, other: Any) -> "RF":
        o = RF.coerce(other)
        if self.den == o.den:
            return RF(self.num + o.num, self.den)
        return RF(self.num * o.den + o.num * self.den, self.den * o.den)

    __radd__ = __add__

    def __neg__(self) -> "RF":
        return RF(-self.num, self.den)

    def __sub__(self, other: Any) -> "RF":
        return self + (-RF.coerce(other))

    def __rsub__(self, other: Any) -> "RF":
        return RF.coerce(other) - self

    def __mul__(self, other: Any) -> "RF":
        o = RF.coerce(other)
        return RF(self.num * o.num, self.den * o.den)

    __rmul__ = __mul__

    def inv(self) -> "RF":
        if self.num.is_zero():
            raise ZeroDivisionError("formal reciprocal of zero")
        return RF(self.den, self.num)

    def __truediv__(self, other: Any) -> "RF":
        return self * RF.coerce(other).inv()

    def __rtruediv__(self, other: Any) -> "RF":
        return RF.coerce(other) / self

    def __pow__(self, n: int) -> "RF":
        if n < 0:
            return self.inv() ** (-n)
        out = RF.coerce(1)
        b = self
        k = n
        while k:
            if k & 1:
                out = out * b
            b = b * b
            k >>= 1
        return out

    def residue_against(self, other: Any) -> LP:
        o = RF.coerce(other)
        return self.num * o.den - o.num * self.den


# ---------- Angles and trigonometric interpretation ----------

@dataclass(frozen=True)
class Angle:
    coeffs: tuple[tuple[str, int], ...] = ()
    quarter: int = 0  # multiples of pi/2

    @staticmethod
    def var(name: str) -> "Angle":
        return Angle(((name, 1),), 0)

    @staticmethod
    def q(k: int = 1) -> "Angle":
        return Angle((), k)

    @staticmethod
    def _make(d: dict[str, int], q: int) -> "Angle":
        return Angle(tuple(sorted((k, v) for k, v in d.items() if v)), q)

    def __add__(self, other: "Angle") -> "Angle":
        d = dict(self.coeffs)
        for k, v in other.coeffs:
            d[k] = d.get(k, 0) + v
            if d[k] == 0:
                del d[k]
        return Angle._make(d, self.quarter + other.quarter)

    def __neg__(self) -> "Angle":
        return Angle(tuple((k, -v) for k, v in self.coeffs), -self.quarter)

    def __sub__(self, other: "Angle") -> "Angle":
        return self + (-other)

    def __rmul__(self, n: int) -> "Angle":
        if not isinstance(n, int):
            return NotImplemented
        return Angle(tuple((k, n * v) for k, v in self.coeffs), n * self.quarter)


def Cis(a: Angle) -> LP:
    coeff = I ** a.quarter
    m: Monomial = tuple((f"z_{name}", exponent) for name, exponent in a.coeffs if exponent != 0)
    return LP.from_dict({m: coeff})


def Sin(a: Angle) -> LP:
    return (Cis(a) - Cis(-a)).divide_constant(2 * I)


def Cos(a: Angle) -> LP:
    return (Cis(a) + Cis(-a)).divide_constant(GQ(2))


def Tan(a: Angle) -> RF:
    return RF(Sin(a), Cos(a))


def Cot(a: Angle) -> RF:
    return RF(Cos(a), Sin(a))


def Sec(a: Angle) -> RF:
    return RF(LP.const(1), Cos(a))


def Csc(a: Angle) -> RF:
    return RF(LP.const(1), Sin(a))


def Var(name: str) -> LP:
    return LP.var(name)


def prod_expr(xs: Iterable[Any]) -> RF:
    out = RF.coerce(1)
    for x in xs:
        out = out * x
    return out


def sum_expr(xs: Iterable[Any]) -> RF:
    out = RF.coerce(0)
    for x in xs:
        out = out + x
    return out


def elementary_symmetric(xs: list[Any], k: int) -> RF:
    e = [RF.coerce(0) for _ in range(k + 1)]
    e[0] = RF.coerce(1)
    for x in xs:
        for j in range(k, 0, -1):
            e[j] = e[j] + e[j - 1] * x
    return e[k]


records: list[dict[str, Any]] = []


def check(name: str, lhs: Any, rhs: Any, family: str, note: str = "") -> None:
    residue = RF.coerce(lhs).residue_against(rhs)
    ok = residue.is_zero()
    records.append({
        "name": name,
        "family": family,
        "ok": ok,
        "residue_terms": len(residue.terms),
        "note": note,
    })
    if not ok:
        raise AssertionError(f"{name}: {residue.text()}")
    if len(records) % 25 == 0:
        print(f"verified {len(records)} identities", flush=True)


# ---------- Identity catalog ----------

def run() -> None:
    a, b, x, h = map(Angle.var, ["a", "b", "x", "h"])
    zero = Angle()
    q = Angle.q(1)
    pi = Angle.q(2)
    tau = Angle.q(4)

    # Basic, reflections, and periodicity.
    check("sin_zero", Sin(zero), 0, "basic")
    check("cos_zero", Cos(zero), 1, "basic")
    check("pythagorean", Sin(x) ** 2 + Cos(x) ** 2, 1, "basic")
    check("sin_neg", Sin(-x), -Sin(x), "symmetry")
    check("cos_neg", Cos(-x), Cos(x), "symmetry")
    check("sin_pi_minus", Sin(pi - x), Sin(x), "reflection")
    check("cos_pi_minus", Cos(pi - x), -Cos(x), "reflection")
    check("sin_q_minus", Sin(q - x), Cos(x), "reflection")
    check("cos_q_minus", Cos(q - x), Sin(x), "reflection")
    check("sin_shift_q_plus", Sin(x + q), Cos(x), "shift")
    check("sin_shift_q_minus", Sin(x - q), -Cos(x), "shift")
    check("cos_shift_q_plus", Cos(x + q), -Sin(x), "shift")
    check("cos_shift_q_minus", Cos(x - q), Sin(x), "shift")
    check("sin_shift_pi", Sin(x + pi), -Sin(x), "periodicity")
    check("cos_shift_pi", Cos(x + pi), -Cos(x), "periodicity")
    check("sin_period_tau", Sin(x + tau), Sin(x), "periodicity")
    check("cos_period_tau", Cos(x + tau), Cos(x), "periodicity")

    # Angle addition and quotient forms.
    check("sin_add", Sin(a + b), Sin(a) * Cos(b) + Cos(a) * Sin(b), "addition")
    check("sin_sub", Sin(a - b), Sin(a) * Cos(b) - Cos(a) * Sin(b), "addition")
    check("cos_add", Cos(a + b), Cos(a) * Cos(b) - Sin(a) * Sin(b), "addition")
    check("cos_sub", Cos(a - b), Cos(a) * Cos(b) + Sin(a) * Sin(b), "addition")
    check("tan_add", Tan(a + b), (Tan(a) + Tan(b)) / (1 - Tan(a) * Tan(b)), "quotient")
    check("tan_sub", Tan(a - b), (Tan(a) - Tan(b)) / (1 + Tan(a) * Tan(b)), "quotient")
    check("cot_add", Cot(a + b), (Cot(a) * Cot(b) - 1) / (Cot(a) + Cot(b)), "quotient")
    check("cot_sub", Cot(a - b), (Cot(a) * Cot(b) + 1) / (Cot(b) - Cot(a)), "quotient")
    check("sec_add", Sec(a + b), Sec(a) * Sec(b) / (1 - Tan(a) * Tan(b)), "quotient")
    check("csc_add", Csc(a + b), Sec(a) * Sec(b) / (Tan(a) + Tan(b)), "quotient")

    # Multiple angles.
    check("sin_double", Sin(2 * x), 2 * Sin(x) * Cos(x), "multiple-angle")
    check("cos_double_1", Cos(2 * x), Cos(x) ** 2 - Sin(x) ** 2, "multiple-angle")
    check("cos_double_2", Cos(2 * x), 2 * Cos(x) ** 2 - 1, "multiple-angle")
    check("cos_double_3", Cos(2 * x), 1 - 2 * Sin(x) ** 2, "multiple-angle")
    check("tan_double", Tan(2 * x), 2 * Tan(x) / (1 - Tan(x) ** 2), "multiple-angle")
    check("cot_double", Cot(2 * x), (Cot(x) ** 2 - 1) / (2 * Cot(x)), "multiple-angle")
    check("sec_double", Sec(2 * x), Sec(x) ** 2 / (2 - Sec(x) ** 2), "multiple-angle")
    check("csc_double", Csc(2 * x), Sec(x) * Csc(x) / 2, "multiple-angle")
    check("sin_triple", Sin(3 * x), 3 * Sin(x) - 4 * Sin(x) ** 3, "multiple-angle")
    check("cos_triple", Cos(3 * x), 4 * Cos(x) ** 3 - 3 * Cos(x), "multiple-angle")
    check("tan_triple", Tan(3 * x), (3 * Tan(x) - Tan(x) ** 3) / (1 - 3 * Tan(x) ** 2), "multiple-angle")
    check("sec_triple", Sec(3 * x), Sec(x) ** 3 / (4 - 3 * Sec(x) ** 2), "multiple-angle")
    check("csc_triple", Csc(3 * x), Csc(x) ** 3 / (3 * Csc(x) ** 2 - 4), "multiple-angle")

    for n in range(0, 11):
        s_rhs = sum_expr(((-1) ** ((k - 1) // 2)) * comb(n, k) * Cos(x) ** (n - k) * Sin(x) ** k
                         for k in range(1, n + 1, 2))
        c_rhs = sum_expr(((-1) ** (k // 2)) * comb(n, k) * Cos(x) ** (n - k) * Sin(x) ** k
                         for k in range(0, n + 1, 2))
        check(f"sin_multiple_binomial_n{n}", Sin(n * x), s_rhs, "multiple-angle-schema")
        check(f"cos_multiple_binomial_n{n}", Cos(n * x), c_rhs, "multiple-angle-schema")

    for n in range(2, 12):
        check(f"cos_chebyshev_recurrence_n{n}", Cos(n * x),
              2 * Cos(x) * Cos((n - 1) * x) - Cos((n - 2) * x), "chebyshev")
        check(f"sin_chebyshev_recurrence_n{n}", Sin(n * x),
              2 * Cos(x) * Sin((n - 1) * x) - Sin((n - 2) * x), "chebyshev")

    # Half-angle and Weierstrass substitution.
    theta = 2 * h
    check("half_angle_sin_squared", Sin(h) ** 2, (1 - Cos(theta)) / 2, "half-angle")
    check("half_angle_cos_squared", Cos(h) ** 2, (1 + Cos(theta)) / 2, "half-angle")
    check("half_angle_tan_1", Tan(h), Sin(theta) / (1 + Cos(theta)), "half-angle")
    check("half_angle_tan_2", Tan(h), (1 - Cos(theta)) / Sin(theta), "half-angle")
    check("half_angle_cot_1", Cot(h), Sin(theta) / (1 - Cos(theta)), "half-angle")
    check("half_angle_cot_2", Cot(h), (1 + Cos(theta)) / Sin(theta), "half-angle")
    t = Tan(h)
    check("weierstrass_sin", Sin(theta), 2 * t / (1 + t ** 2), "tangent-half-angle")
    check("weierstrass_cos", Cos(theta), (1 - t ** 2) / (1 + t ** 2), "tangent-half-angle")
    check("weierstrass_cis", Cis(theta), (1 + RF.coerce(I) * t) / (1 - RF.coerce(I) * t), "tangent-half-angle")

    # Product-to-sum and sum-to-product.
    check("cos_cos_product", Cos(a) * Cos(b), (Cos(a - b) + Cos(a + b)) / 2, "product-to-sum")
    check("sin_sin_product", Sin(a) * Sin(b), (Cos(a - b) - Cos(a + b)) / 2, "product-to-sum")
    check("sin_cos_product", Sin(a) * Cos(b), (Sin(a + b) + Sin(a - b)) / 2, "product-to-sum")
    check("cos_sin_product", Cos(a) * Sin(b), (Sin(a + b) - Sin(a - b)) / 2, "product-to-sum")
    p, r = Angle.var("p"), Angle.var("r")
    theta2, phi2 = p + r, p - r
    check("sin_add_sum_to_product", Sin(theta2) + Sin(phi2), 2 * Sin(p) * Cos(r), "sum-to-product")
    check("sin_sub_sum_to_product", Sin(theta2) - Sin(phi2), 2 * Cos(p) * Sin(r), "sum-to-product")
    check("cos_add_sum_to_product", Cos(theta2) + Cos(phi2), 2 * Cos(p) * Cos(r), "sum-to-product")
    check("cos_sub_sum_to_product", Cos(theta2) - Cos(phi2), -2 * Sin(p) * Sin(r), "sum-to-product")
    check("tan_sum_product", Tan(a) + Tan(b), Sin(a + b) / (Cos(a) * Cos(b)), "sum-to-product")
    check("tan_difference_product", Tan(a) - Tan(b), Sin(a - b) / (Cos(a) * Cos(b)), "sum-to-product")

    for n in range(1, 7):
        angles = [Angle.var(f"u{n}_{j}") for j in range(n)]
        lhs_cos = prod_expr(Cos(v) for v in angles)
        signed_cos = RF.coerce(0)
        signed_sin_complex = RF.coerce(0)
        for signs in product((-1, 1), repeat=n):
            total = Angle()
            weight = 1
            for sign, v in zip(signs, angles):
                total = total + sign * v
                weight *= sign
            signed_cos += Cos(total)
            signed_sin_complex += weight * Cis(total)
        check(f"general_cos_product_n{n}", lhs_cos, signed_cos / (2 ** n), "product-to-sum-schema")
        check(f"general_sin_product_n{n}", prod_expr(Sin(v) for v in angles),
              signed_sin_complex / ((2 * I) ** n), "product-to-sum-schema")

    # Power reduction.
    check("sin_sq_reduction", Sin(x) ** 2, (1 - Cos(2 * x)) / 2, "power-reduction")
    check("cos_sq_reduction", Cos(x) ** 2, (1 + Cos(2 * x)) / 2, "power-reduction")
    check("sin_cube_reduction", Sin(x) ** 3, (3 * Sin(x) - Sin(3 * x)) / 4, "power-reduction")
    check("cos_cube_reduction", Cos(x) ** 3, (3 * Cos(x) + Cos(3 * x)) / 4, "power-reduction")
    check("sin_fourth_reduction", Sin(x) ** 4, (3 - 4 * Cos(2 * x) + Cos(4 * x)) / 8, "power-reduction")
    check("cos_fourth_reduction", Cos(x) ** 4, (3 + 4 * Cos(2 * x) + Cos(4 * x)) / 8, "power-reduction")
    check("sin_fifth_reduction", Sin(x) ** 5,
          (10 * Sin(x) - 5 * Sin(3 * x) + Sin(5 * x)) / 16, "power-reduction")
    check("cos_fifth_reduction", Cos(x) ** 5,
          (10 * Cos(x) + 5 * Cos(3 * x) + Cos(5 * x)) / 16, "power-reduction")

    # Finite angle sums via elementary symmetric polynomials.
    # Four-variable regressions keep exact rational-function normalization fast;
    # the report proves the schema for arbitrary n by finite induction.
    for n in range(1, 5):
        angles = [Angle.var(f"t{n}_{j}") for j in range(n)]
        tans = [Tan(v) for v in angles]
        odd = sum_expr(((-1) ** ((k - 1) // 2)) * elementary_symmetric(tans, k)
                       for k in range(1, n + 1, 2))
        even = sum_expr(((-1) ** (k // 2)) * elementary_symmetric(tans, k)
                        for k in range(0, n + 1, 2))
        total = Angle()
        for v in angles:
            total = total + v
        check(f"tangent_symmetric_sum_n{n}", Tan(total), odd / even, "finite-angle-sums")
        check(f"secant_symmetric_sum_n{n}", Sec(total), prod_expr(Sec(v) for v in angles) / even,
              "finite-angle-sums")
        check(f"cosecant_symmetric_sum_n{n}", Csc(total), prod_expr(Sec(v) for v in angles) / odd,
              "finite-angle-sums")

    # Lagrange, Dirichlet, and arithmetic progression sums.
    for n in range(0, 11):
        hh = Angle.var(f"lh{n}")
        check(f"lagrange_sine_n{n}", sum_expr(Sin((2 * k) * hh) for k in range(n + 1)),
              (Cos(hh) - Cos((2 * n + 1) * hh)) / (2 * Sin(hh)), "finite-sums")
        check(f"lagrange_cosine_n{n}", sum_expr(Cos((2 * k) * hh) for k in range(1, n + 1)),
              (-Sin(hh) + Sin((2 * n + 1) * hh)) / (2 * Sin(hh)), "finite-sums")
        check(f"dirichlet_kernel_n{n}", 1 + 2 * sum_expr(Cos((2 * k) * hh) for k in range(1, n + 1)),
              Sin((2 * n + 1) * hh) / Sin(hh), "finite-sums")
    for n in range(1, 11):
        aa = Angle.var(f"odd{n}")
        check(f"odd_cosine_sum_n{n}", sum_expr(Cos((2 * k - 1) * aa) for k in range(1, n + 1)),
              Sin((2 * n) * aa) / (2 * Sin(aa)), "finite-sums")
    for n in range(0, 9):
        aa, hh = Angle.var(f"ap_a{n}"), Angle.var(f"ap_h{n}")
        check(f"arithmetic_sine_sum_n{n}", sum_expr(Sin(aa + (2 * k) * hh) for k in range(n + 1)),
              Sin((n + 1) * hh) / Sin(hh) * Sin(aa + n * hh), "arithmetic-progressions")
        check(f"arithmetic_cosine_sum_n{n}", sum_expr(Cos(aa + (2 * k) * hh) for k in range(n + 1)),
              Sin((n + 1) * hh) / Sin(hh) * Cos(aa + n * hh), "arithmetic-progressions")

    # Finite Viète product.
    for n in range(1, 10):
        base = Angle.var(f"v{n}")
        check(f"viete_finite_n{n}", prod_expr(Cos((2 ** (n - j)) * base) for j in range(1, n + 1)),
              Sin((2 ** n) * base) / ((2 ** n) * Sin(base)), "finite-products")

    # Linear fractional transformations and harmonic coefficients.
    X = Var("X")
    f_b = (Cos(b) * X - Sin(b)) / (Sin(b) * X + Cos(b))
    composed = (RF.coerce(Cos(a)) * f_b - Sin(a)) / (RF.coerce(Sin(a)) * f_b + Cos(a))
    target = (Cos(a + b) * X - Sin(a + b)) / (Sin(a + b) * X + Cos(a + b))
    check("linear_fractional_rotation", composed, target, "linear-fractional")
    A, B, C = Var("A"), Var("B"), Var("C")
    ph = Angle.var("ph")
    check("linear_combination_expansion", C * Cos(x + ph),
          C * Cos(ph) * Cos(x) - C * Sin(ph) * Sin(x), "linear-combinations")
    u, v = Angle.var("u"), Angle.var("v")
    amp_cos = A * Cos(u) + B * Cos(v)
    amp_sin = A * Sin(u) + B * Sin(v)
    check("two_phase_amplitude_square", amp_cos ** 2 + amp_sin ** 2,
          A ** 2 + B ** 2 + 2 * A * B * Cos(u - v), "linear-combinations")

    # Hermite's finite cotangent partial fraction identity (small regressions).
    zz = Angle.var("hz")
    for n in (2, 3):
        aks = [Angle.var(f"ha{n}_{j}") for j in range(n)]
        lhs = prod_expr(Cot(zz - ak) for ak in aks)
        rhs = RF.coerce(Cos(Angle.q(n)))
        for k, ak in enumerate(aks):
            coeff = prod_expr(Cot(ak - aj) for j, aj in enumerate(aks) if j != k)
            rhs += coeff * Cot(zz - ak)
        check(f"hermite_cotangent_n{n}", lhs, rhs, "hermite")

    # Triangle identities, alpha+beta+gamma=pi.
    al, be = Angle.var("tri_a"), Angle.var("tri_b")
    ga = pi - al - be
    check("triangle_tangent_sum", Tan(al) + Tan(be) + Tan(ga),
          Tan(al) * Tan(be) * Tan(ga), "triangle")
    check("triangle_cot_pair_sum", 1,
          Cot(be) * Cot(ga) + Cot(ga) * Cot(al) + Cot(al) * Cot(be), "triangle")
    Aang, Bang = Angle.var("tri_A"), Angle.var("tri_B")
    Cang = q - Aang - Bang
    alpha, beta, gamma = 2 * Aang, 2 * Bang, 2 * Cang
    check("triangle_half_cot_sum", Cot(Aang) + Cot(Bang) + Cot(Cang),
          Cot(Aang) * Cot(Bang) * Cot(Cang), "triangle")
    check("triangle_half_tan_pairs", 1,
          Tan(Bang) * Tan(Cang) + Tan(Cang) * Tan(Aang) + Tan(Aang) * Tan(Bang), "triangle")
    check("triangle_sine_sum", Sin(alpha) + Sin(beta) + Sin(gamma),
          4 * Cos(Aang) * Cos(Bang) * Cos(Cang), "triangle")
    check("triangle_sine_signed", -Sin(alpha) + Sin(beta) + Sin(gamma),
          4 * Cos(Aang) * Sin(Bang) * Sin(Cang), "triangle")
    check("triangle_cosine_sum", Cos(alpha) + Cos(beta) + Cos(gamma),
          1 + 4 * Sin(Aang) * Sin(Bang) * Sin(Cang), "triangle")
    check("triangle_cosine_signed", -Cos(alpha) + Cos(beta) + Cos(gamma),
          -1 + 4 * Sin(Aang) * Cos(Bang) * Cos(Cang), "triangle")
    check("triangle_double_sine_sum", Sin(2 * alpha) + Sin(2 * beta) + Sin(2 * gamma),
          4 * Sin(alpha) * Sin(beta) * Sin(gamma), "triangle")
    check("triangle_double_sine_signed", -Sin(2 * alpha) + Sin(2 * beta) + Sin(2 * gamma),
          4 * Sin(alpha) * Cos(beta) * Cos(gamma), "triangle")
    check("triangle_double_cosine_sum", Cos(2 * alpha) + Cos(2 * beta) + Cos(2 * gamma),
          -1 - 4 * Cos(alpha) * Cos(beta) * Cos(gamma), "triangle")
    check("triangle_double_cosine_signed", -Cos(2 * alpha) + Cos(2 * beta) + Cos(2 * gamma),
          1 - 4 * Cos(alpha) * Sin(beta) * Sin(gamma), "triangle")
    check("triangle_sin_sq_sum", Sin(alpha) ** 2 + Sin(beta) ** 2 + Sin(gamma) ** 2,
          2 + 2 * Cos(alpha) * Cos(beta) * Cos(gamma), "triangle")
    check("triangle_sin_sq_signed", -Sin(alpha) ** 2 + Sin(beta) ** 2 + Sin(gamma) ** 2,
          2 * Cos(alpha) * Sin(beta) * Sin(gamma), "triangle")
    check("triangle_cos_sq_sum", Cos(alpha) ** 2 + Cos(beta) ** 2 + Cos(gamma) ** 2,
          1 - 2 * Cos(alpha) * Cos(beta) * Cos(gamma), "triangle")
    check("triangle_cos_sq_signed", -Cos(alpha) ** 2 + Cos(beta) ** 2 + Cos(gamma) ** 2,
          1 - 2 * Cos(alpha) * Sin(beta) * Sin(gamma), "triangle")
    check("triangle_half_sin_sq", 1,
          Sin(Aang) ** 2 + Sin(Bang) ** 2 + Sin(Cang) ** 2 +
          2 * Sin(Aang) * Sin(Bang) * Sin(Cang), "triangle")

    # Euler identities are definitional in this model.
    check("euler_cos", Cos(x), (Cis(x) + Cis(-x)) / 2, "complex-exponential")
    check("euler_sin", Sin(x), (Cis(x) - Cis(-x)) / (2 * I), "complex-exponential")

    failures = [r for r in records if not r["ok"]]
    families: dict[str, int] = {}
    for r in records:
        families[r["family"]] = families.get(r["family"], 0) + 1
    summary = {"checks": len(records), "failures": len(failures),
               "families": dict(sorted(families.items()))}
    out_dir = Path(__file__).resolve().parents[1] / "artifacts"
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "identity_certificates.json").write_text(
        json.dumps({"summary": summary, "records": records}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    lines = [
        "Exact Laurent-polynomial identity verification",
        "==============================================",
        f"checks:   {summary['checks']}",
        f"failures: {summary['failures']}",
        "",
        "checks by family:",
    ] + [f"  {k}: {v}" for k, v in summary["families"].items()] + [
        "", "All residues reduced to the zero Laurent polynomial."
    ]
    (out_dir / "verification_report.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    run()
