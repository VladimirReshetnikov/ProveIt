#!/usr/bin/env python3
"""Exact symbolic audit for the constructive iPRA geometry packet.

The checks use SymPy only as an independent development-time auditor.  Each
identity is polynomial (or a rational identity with denominators recorded as
positive in the report).  The intended iPRA checker is the much smaller
coefficient-list normalizer described in the paper; no numerical floating
point arithmetic occurs here.
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable

import sympy as sp

HERE = Path(__file__).resolve().parent

passed: list[str] = []


def check_zero(name: str, expr: sp.Expr) -> None:
    value = sp.expand(expr)
    if value != 0:
        raise AssertionError(f"{name}: nonzero remainder: {value}")
    passed.append(name)
    print(f"PASS {name}")


def check_simplify_zero(name: str, expr: sp.Expr) -> None:
    value = sp.factor(sp.cancel(expr))
    if value != 0:
        raise AssertionError(f"{name}: nonzero remainder: {value}")
    passed.append(name)
    print(f"PASS {name}")


def check_ideal_zero(
    name: str,
    expr: sp.Expr,
    generators: Iterable[sp.Expr],
    variables: Iterable[sp.Symbol],
) -> None:
    G = sp.groebner(list(generators), *list(variables), order="grevlex")
    _, rem = G.reduce(sp.expand(expr))
    rem = sp.expand(rem)
    if rem != 0:
        raise AssertionError(f"{name}: ideal remainder: {rem}")
    passed.append(name)
    print(f"PASS {name}")


# ---------------------------------------------------------------------------
# Triangle side and half-angle bridge
# ---------------------------------------------------------------------------
x, y, z = sp.symbols("x y z")
s = x + y + z
a = y + z
b = z + x
c = x + y

check_zero("semiperimeter_x", s - a - x)
check_zero("semiperimeter_y", s - b - y)
check_zero("semiperimeter_z", s - c - z)
check_zero("half_angle_A_unit_numerator", y * z + s * x - b * c)
check_zero("half_angle_B_unit_numerator", z * x + s * y - c * a)
check_zero("half_angle_C_unit_numerator", x * y + s * z - a * b)

# Positive-square-root product identities used to prove A/2+B/2+C/2=pi/2.
# The roots themselves do not appear: we compare the squares of both positive
# sides after substituting their defining radicands.
sA2, cA2 = y * z / (b * c), s * x / (b * c)
sB2, cB2 = z * x / (c * a), s * y / (c * a)
sC2, cC2 = x * y / (a * b), s * z / (a * b)
check_simplify_zero("complement_c_sA_cB", c**2 * sA2 * cB2 - y**2 * cC2)
check_simplify_zero("complement_c_cA_sB", c**2 * cA2 * sB2 - x**2 * cC2)
check_simplify_zero("complement_s_cA_cB", c**2 * cA2 * cB2 - s**2 * sC2)
check_simplify_zero("complement_z_sA_sB", c**2 * sA2 * sB2 - z**2 * sC2)

# Heron/area and sine-scale radicands.
check_simplify_zero("sine_A_area_product", (b * c) ** 2 * sA2 * cA2 - s * x * y * z)
check_simplify_zero("sine_B_area_product", (c * a) ** 2 * sB2 * cB2 - s * x * y * z)
check_simplify_zero("sine_C_area_product", (a * b) ** 2 * sC2 * cC2 - s * x * y * z)

# ---------------------------------------------------------------------------
# Mollweide and tangent law: denominator-free polynomial core
# ---------------------------------------------------------------------------
sA, cA, sB, cB, sC, cC, d = sp.symbols("sA cA sB cB sC cC d")
A_side, B_side, C_side = sp.symbols("a b c")
sD = sA * cB - cA * sB
cD = cA * cB + sA * sB

h_unit_A = sA**2 + cA**2 - 1
h_unit_B = sB**2 + cB**2 - 1
h_compl_cos = cC - (sA * cB + cA * sB)
h_compl_sin = sC - (cA * cB - sA * sB)
h_side_A = A_side - 2 * d * sA * cA
h_side_B = B_side - 2 * d * sB * cB
h_side_C = C_side - 2 * d * sC * cC

tri_vars = [A_side, B_side, C_side, d, sC, cC, sA, cA, sB, cB]
tri_hyp = [
    h_unit_A,
    h_unit_B,
    h_compl_cos,
    h_compl_sin,
    h_side_A,
    h_side_B,
    h_side_C,
]

moll_sum = (A_side + B_side) * sC - C_side * cD
moll_diff = (A_side - B_side) * cC - C_side * sD
check_ideal_zero("mollweide_sum_cross", moll_sum, tri_hyp, tri_vars)
check_ideal_zero("mollweide_difference_cross", moll_diff, tri_hyp, tri_vars)

law_tangent_cross = (
    (A_side - B_side) * cD * cC
    - (A_side + B_side) * sD * sC
)
check_zero("law_of_tangents_from_mollweide", law_tangent_cross - (cD * moll_diff - sD * moll_sum))
check_ideal_zero("law_of_tangents_cross", law_tangent_cross, tri_hyp, tri_vars)

# ---------------------------------------------------------------------------
# Cotangent law and inradius identity
# ---------------------------------------------------------------------------
r, hA, hB, hC = sp.symbols("r hA hB hC")
xA, xB, xC, semi = sp.symbols("xA xB xC semi")
sAh, cAh, sBh, cBh, sCh, cCh = sp.symbols("sAh cAh sBh cBh sCh cCh")

check_zero(
    "cotangent_A_right_triangle",
    (hA * sAh) * cAh - (hA * cAh) * sAh,
)
check_zero(
    "cotangent_B_right_triangle",
    (hB * sBh) * cBh - (hB * cBh) * sBh,
)
check_zero(
    "cotangent_C_right_triangle",
    (hC * sCh) * cCh - (hC * cCh) * sCh,
)

# A certificate for the denominator-free inradius formula.  The assumptions
# eA=eB=eC=0 are r*c_i=x_i*s_i; eS=0 is semi=xA+xB+xC;
# eT=0 is cos(A/2+B/2+C/2)=0.
eA = r * cAh - xA * sAh
eB = r * cBh - xB * sBh
eC = r * cCh - xC * sCh
eS = semi - (xA + xB + xC)
eT = (
    cAh * cBh * cCh
    - cAh * sBh * sCh
    - sAh * cBh * sCh
    - sAh * sBh * cCh
)
prod_s = sAh * sBh * sCh
inradius_target = (r**2 * semi - xA * xB * xC) * prod_s
qA = r**2 * (cBh * cCh - sBh * sCh)
qB = r * sAh * (xA * cCh - r * sCh)
qC = sAh * sBh * (xA * xB - r**2)
certificate = qA * eA + qB * eB + qC * eC - r**3 * eT + r**2 * prod_s * eS
check_zero("inradius_denominator_free_certificate", inradius_target - certificate)

# ---------------------------------------------------------------------------
# Power of a point: coordinate identities
# ---------------------------------------------------------------------------
px, py, ox, oy, vx, vy, t, u, w, rho = sp.symbols(
    "px py ox oy vx vy t u w rho"
)

def nsq(X: sp.Expr, Y: sp.Expr) -> sp.Expr:
    return X**2 + Y**2


def dot(X: sp.Expr, Y: sp.Expr, U: sp.Expr, V: sp.Expr) -> sp.Expr:
    return X * U + Y * V

p = nsq(px - ox, py - oy) - rho
h = dot(px - ox, py - oy, vx, vy)
q = nsq(vx, vy)
line_power = nsq(px + t * vx - ox, py + t * vy - oy) - rho
f = p + 2 * h * t + q * t**2
check_zero("power_line_expansion", line_power - f)

fu = p + 2 * h * u + q * u**2
fw = p + 2 * h * w + q * w**2
check_zero("secant_factor_identity", w * fu - u * fw - (w - u) * (p - q * u * w))

# Tangent point T and base point P=T-tV.
tx, ty = sp.symbols("tx ty")
tangent_power = nsq(tx - t * vx - ox, ty - t * vy - oy) - rho
on_circle = nsq(tx - ox, ty - oy) - rho
perp = dot(tx - ox, ty - oy, vx, vy)
check_zero(
    "tangent_power_decomposition",
    tangent_power - (q * t**2 + on_circle - 2 * t * perp),
)

# The line through a tangent point has only that intersection when q is apart
# from zero: the residual circle equation is q*(lambda-t)^2.
lam = sp.symbols("lam")
tangent_line_residual = nsq(tx + (lam - t) * vx - ox, ty + (lam - t) * vy - oy) - rho
check_zero(
    "tangent_unique_intersection_residual",
    tangent_line_residual - (on_circle + 2 * (lam - t) * perp + q * (lam - t) ** 2),
)

# Corollary equalities once each product is identified with the same power.
pow0 = sp.symbols("pow0")
alpha, beta, gamma, delta, tau = sp.symbols("alpha beta gamma delta tau")
check_zero("intersecting_secants_core", (alpha * delta - beta * gamma) - ((alpha * delta - pow0) - (beta * gamma - pow0)))
check_zero("intersecting_chords_core", (alpha * gamma - beta * delta) - ((pow0 + alpha * gamma) - (pow0 + beta * delta)))
check_zero("tangent_secant_core", (tau**2 - alpha * beta) - ((tau**2 - pow0) - (alpha * beta - pow0)))

# ---------------------------------------------------------------------------
# Exact worked examples (Fractions only)
# ---------------------------------------------------------------------------
def q2(fr: Fraction) -> str:
    return f"{fr.numerator}/{fr.denominator}"

# Circle x^2+y^2=25, P=(13,0).  Rational tangent T and a rational secant.
P = (Fraction(13), Fraction(0))
T = (Fraction(25, 13), Fraction(60, 13))
A = (Fraction(3), Fraction(4))
B = (Fraction(17, 29), Fraction(144, 29))


def dist_sq(P0, Q0):
    return (P0[0] - Q0[0]) ** 2 + (P0[1] - Q0[1]) ** 2

assert dist_sq(T, (Fraction(0), Fraction(0))) == 25
assert dist_sq(A, (Fraction(0), Fraction(0))) == 25
assert dist_sq(B, (Fraction(0), Fraction(0))) == 25
assert dist_sq(P, T) == 144
# Parameter product in the non-unit chart V=A-P: first root 1, second 36/29.
V = (A[0] - P[0], A[1] - P[1])
qV = V[0] ** 2 + V[1] ** 2
assert qV == 116
assert qV * Fraction(36, 29) == 144
passed.append("worked_tangent_secant_fraction_example")
print("PASS worked_tangent_secant_fraction_example")

# Chords through S=(1,0): x-axis gives 6*4=24; the line through (3,4)
# has the second rational point (-7/5,-24/5) and parameter product -6/5.
S = (Fraction(1), Fraction(0))
C1 = (Fraction(3), Fraction(4))
C2 = (Fraction(-7, 5), Fraction(-24, 5))
assert dist_sq(C1, (Fraction(0), Fraction(0))) == 25
assert dist_sq(C2, (Fraction(0), Fraction(0))) == 25
VC = (C1[0] - S[0], C1[1] - S[1])
qC = VC[0] ** 2 + VC[1] ** 2
assert qC == 20
assert qC * Fraction(-6, 5) == -24
passed.append("worked_intersecting_chords_fraction_example")
print("PASS worked_intersecting_chords_fraction_example")

summary = {
    "status": "pass",
    "count": len(passed),
    "checks": passed,
    "notes": [
        "All symbolic checks are exact.",
        "Rational worked examples use fractions.Fraction, not floating point.",
        "The script is an audit, not a substitute for the proposed iPRA proof objects.",
    ],
}
(HERE / "results.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
print(f"ALL CERTIFICATES PASS ({len(passed)} checks)")
