#!/usr/bin/env python3
"""Independent exact and numerical checks for the weighted arctangent section.

The analytic proofs are in weighted_arctangent.tex.  Numerical comparisons
are audits, not certificates of exact special-value equality.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import sympy as sp


OUTPUT = (Path(__file__).resolve().parent.parent / 'results' / 'weighted_arctangent_verification.json')
mp.mp.dps = 80
records: list[dict] = []


def record(kind, parameters, left, right):
    err = abs(left - right)
    assert err < mp.mpf("1e-70"), (kind, parameters, mp.nstr(err, 20))
    records.append(
        {
            "kind": kind,
            "parameters": parameters,
            "left": mp.nstr(left, 76),
            "right": mp.nstr(right, 76),
            "absolute_error": mp.nstr(err, 12),
        }
    )


def chi(n, z):
    return (mp.polylog(n, z) - mp.polylog(n, -z)) / 2


def F_hyperbolic(s):
    s = abs(s)
    if s == 0:
        return mp.mpf(0)
    return mp.pi**2 * s / 8 - 7 * mp.zeta(3) / 4 + s * chi(2, mp.exp(-s)) + 2 * chi(3, mp.exp(-s))


def K_hyperbolic(p, q):
    alpha, beta = mp.asinh(p), mp.asinh(q)
    return F_hyperbolic(alpha + beta) - F_hyperbolic(alpha - beta)


def sinh_quotient(s):
    return s / mp.sinh(s) if s else mp.mpf(1)


def G_trigonometric(t):
    if t == 0:
        return mp.mpf(0)
    if abs(t) == mp.pi:
        return 7 * mp.zeta(3) / 2
    z = mp.exp(mp.j * t)
    return 7 * mp.zeta(3) / 4 - t * mp.im(chi(2, z)) - 2 * mp.re(chi(3, z))


def L_atanh(r, s):
    a, b = mp.asin(r), mp.asin(s)
    return G_trigonometric(a + b) - G_trigonometric(a - b)


def L_atanh_quad(r, s):
    # u = atanh(sin x) avoids catastrophic rounding of sin x to 1 at
    # the improper endpoint. At |r|=1 the inverse functions cancel.
    def transformed_atanh(parameter, u):
        return parameter * u if abs(parameter) == 1 else mp.atanh(parameter * mp.tanh(u))

    return mp.quad(
        lambda u: transformed_atanh(r, u) * transformed_atanh(s, u) / mp.sinh(u),
        [0, 1, mp.inf],
    )


def P(y, c=1):
    if y == 1:
        return -2 * mp.polylog(3, 1 / mp.mpf(c)) if c == 1 else -2 * mp.polylog(3, 1 / c)
    ly = mp.log(y)
    return (
        ly**2 * mp.log(1 - y / c)
        + 2 * ly * mp.polylog(2, y / c)
        - 2 * mp.polylog(3, y / c)
    )


def L_classical(a, b):
    """Only the branch-safe imaginary arguments of the lemma are admitted."""
    assert mp.re(a) == 0 and mp.re(b) == 0
    assert mp.im(a) > 0 and b != 0
    if a == b:
        return P(1 - a) + 2 * mp.zeta(3)
    if mp.im(b) > 0 and abs(a) < abs(b):
        a, b = b, a
    r = (1 - a) / (1 - b)
    return (
        (P(1 - a) + P(1 - b) - P(r) + P(r, a / b)) / 2
        + mp.zeta(3)
        + mp.polylog(3, b / a)
    )


def J_classical(A, B):
    return mp.re(L_classical(mp.j * A, -mp.j * B) - L_classical(mp.j * A, mp.j * B)) / 2


def I_classical(p, q, T=1):
    a, b = mp.exp(mp.asinh(p)), mp.exp(mp.asinh(q))
    return (
        J_classical(a * T, b * T)
        - J_classical(a * T, T / b)
        - J_classical(T / a, b * T)
        + J_classical(T / a, T / b)
    )


def L_quad(a, b, m=1):
    return mp.quad(
        lambda t: (-mp.log(t)) ** (m - 1) * mp.log(1 - a * t) * mp.log(1 - b * t) / t,
        [0, 1],
    ) / mp.factorial(m - 1)


def Li_r1_series(r, x, y, cutoff=240):
    """Nested sum by outer index, independent of the logarithmic quadrature."""
    inner = mp.mpc(0)
    result = mp.mpc(0)
    x_power, y_power = x, mp.mpc(1)
    for n in range(1, cutoff + 1):
        result += x_power * inner / (mp.mpf(n) ** r)
        y_power *= y
        inner += y_power / n
        x_power *= x
    return result


def L_series(a, b, m=1):
    assert max(abs(a), abs(b)) < mp.mpf("0.4")
    return Li_r1_series(m + 1, a, b / a) + Li_r1_series(m + 1, b, a / b)


def J_series(A, B, m):
    return mp.re(L_series(mp.j * A, -mp.j * B, m) - L_series(mp.j * A, mp.j * B, m)) / 2


def I_series(p, q, T, m):
    a, b = mp.exp(mp.asinh(p)), mp.exp(mp.asinh(q))
    return (
        J_series(a * T, b * T, m)
        - J_series(a * T, T / b, m)
        - J_series(T / a, b * T, m)
        + J_series(T / a, T / b, m)
    )


def I_quad(p, q, T, m):
    # Direct rationalized sine integrand, not the four arctangent differences.
    return mp.quad(
        lambda s: (-mp.log(s)) ** (m - 1)
        * mp.atan(2 * p * T * s / (1 + (T * s) ** 2))
        * mp.atan(2 * q * T * s / (1 + (T * s) ** 2))
        / s,
        [0, 1],
    ) / mp.factorial(m - 1)


def elementary_mixed(p, q):
    if p * p == q * q:
        if p == 0:
            return mp.mpf(1)
        return 1 / (2 * (1 + p * p)) + mp.asinh(p) / (2 * p * (1 + p * p) ** mp.mpf("1.5"))
    return (
        p * mp.asinh(p) / mp.sqrt(1 + p * p)
        - q * mp.asinh(q) / mp.sqrt(1 + q * q)
    ) / (p * p - q * q)


# Exact algebra: the logarithmic primitive differentiation and coefficient
# obstruction are checked independently of all mpmath computations.
y, c = sp.symbols("y c", nonzero=True)
primitive = (
    sp.log(y) ** 2 * sp.log(1 - y / c)
    + 2 * sp.log(y) * sp.polylog(2, y / c)
    - 2 * sp.polylog(3, y / c)
)
primitive_residual = sp.simplify(
    sp.diff(primitive, y).subs(sp.polylog(1, y / c), -sp.log(1 - y / c))
    - sp.log(y) ** 2 / (y - c)
)
assert primitive_residual == 0

alpha, beta, A, B = sp.symbols("alpha beta A B", nonzero=True)
sinha, cosha = (A - 1 / A) / 2, (A + 1 / A) / 2
sinhb, coshb = (B - 1 / B) / 2, (B + 1 / B) / 2
sinhplus, sinhminus = (A * B - 1 / (A * B)) / 2, (A / B - B / A) / 2
hyperbolic_residual = sp.factor(
    (alpha * sinha * coshb - beta * sinhb * cosha) / (sinha**2 - sinhb**2)
    - ((alpha + beta) / sinhplus + (alpha - beta) / sinhminus) / 2
)
assert hyperbolic_residual == 0

sina, cosa = (A - 1 / A) / (2 * sp.I), (A + 1 / A) / 2
sinb, cosb = (B - 1 / B) / (2 * sp.I), (B + 1 / B) / 2
sinplus, sinminus = (A * B - 1 / (A * B)) / (2 * sp.I), (A / B - B / A) / (2 * sp.I)
trigonometric_residual = sp.simplify(
    (alpha * sina * cosb - beta * sinb * cosa) / (sina**2 - sinb**2)
    - ((alpha + beta) / sinplus + (alpha - beta) / sinminus) / 2
)
assert trigonometric_residual == 0

s = sp.symbols("s", positive=True)
exp_s = sp.exp(-s)
F_symbolic = (
    sp.pi**2 * s / 8 - 7 * sp.zeta(3) / 4
    + s * (sp.polylog(2, exp_s) - sp.polylog(2, -exp_s)) / 2
    + sp.polylog(3, exp_s) - sp.polylog(3, -exp_s)
)
F_residual = sp.simplify(sp.expand_func(sp.diff(F_symbolic, s, 2)) - s * exp_s / (1 - exp_s**2))
assert F_residual == 0

p, q = sp.symbols("p q")
K_taylor = sum(
    (-1) ** (j + k)
    * p ** (2 * j + 1)
    * q ** (2 * k + 1)
    * sp.Rational(4 ** (j + k), (2 * j + 1) * (2 * k + 1) * (2 * j + 2 * k + 1) * sp.binomial(2 * j + 2 * k, j + k))
    for j in range(3)
    for k in range(3)
    if j + k <= 2
)
assert sp.expand(K_taylor).coeff(p, 3).coeff(q, 1) == -sp.Rational(2, 9)
assert -sp.Rational(2, 9) + sp.Rational(1, 4) == sp.Rational(1, 36)

u, v = sp.symbols("u v")
K_uv = sp.series(
    sp.series(K_taylor.subs({p: 2 * u / (1 - u * u), q: 2 * v / (1 - v * v)}), u, 0, 4).removeO(),
    v,
    0,
    4,
).removeO().expand()
assert K_uv.coeff(u, 3).coeff(v, 1) == sp.Rational(4, 9)

exact = {
    "primitive_derivative_residual": str(primitive_residual),
    "hyperbolic_addition_residual": str(hyperbolic_residual),
    "trigonometric_addition_residual": str(trigonometric_residual),
    "F_second_derivative_residual": str(F_residual),
    "weighted_p3q_coefficient": "-2/9",
    "predicted_product_ansatz_p3q_coefficient": "-1/4",
    "coefficient_discrepancy": "1/36",
    "transformed_u3v_coefficient": "4/9",
    "taylor_polynomial_through_total_degree_six": str(sp.expand(K_taylor)),
}

for A, B, sign in [
    ("2", "1", 1),
    ("1", "2", 1),
    ("2", "1", -1),
    ("0.2", "3", -1),
    ("0.5", "0.5", 1),
    ("1", "1", -1),
    ("100", "0.1", -1),
    ("0.01", "100", 1),
]:
    a, b = mp.j * mp.mpf(A), mp.j * sign * mp.mpf(B)
    record("classical_log_kernel", [A, B, sign], L_classical(a, b), L_quad(a, b))

for ps, qs in [("1", "1"), ("1", "2"), ("0.2", "0.6"), ("-2", "1"), ("0", "1"), ("10", "0.03")]:
    p, q = mp.mpf(ps), mp.mpf(qs)
    direct = mp.quad(lambda x: mp.atan(p * mp.sin(x)) * mp.atan(q * mp.sin(x)) / mp.sin(x), [0, mp.pi / 2])
    record("weighted_integral", [ps, qs], I_classical(p, q), direct)
    record("hyperbolic_weighted_integral", [ps, qs], K_hyperbolic(p, q), direct)

for ps, qs in [("-0.001", "-0.0001"), ("20", "-10")]:
    p, q = mp.mpf(ps), mp.mpf(qs)
    direct = mp.quad(lambda x: mp.atan(p * mp.sin(x)) * mp.atan(q * mp.sin(x)) / mp.sin(x), [0, mp.pi / 2])
    record("hyperbolic_weighted_integral", [ps, qs], K_hyperbolic(p, q), direct)

for ss in ("0.001", "0.1", "1", "4", "-2"):
    s = abs(mp.mpf(ss))
    direct = mp.quad(lambda t: (s - t) * sinh_quotient(t) / 2, [0, s])
    record("normalized_F_primitive", [ss], F_hyperbolic(mp.mpf(ss)), direct)

ell, r = mp.log(1 + mp.sqrt(2)), 3 - 2 * mp.sqrt(2)
diagonal_closed = mp.pi**2 * ell / 4 - 7 * mp.zeta(3) / 4 + 2 * ell * chi(2, r) + 2 * chi(3, r)
diagonal_direct = mp.quad(lambda x: mp.atan(mp.sin(x))**2 / mp.sin(x), [0, mp.pi / 2])
record("explicit_diagonal", ["p=q=1"], diagonal_closed, diagonal_direct)

beta = mp.log((1 + mp.sqrt(5)) / 2)
cleo_closed = F_hyperbolic(2 * ell) + 2 * F_hyperbolic(ell + beta) - 2 * F_hyperbolic(ell - beta) + F_hyperbolic(2 * beta)
cleo_direct = mp.quad(lambda x: mp.atan(6 * mp.sin(x) / (3 + mp.cos(2 * x)))**2 / mp.sin(x), [0, mp.pi / 2])
record("weighted_Cleo", ["algebraic unit parameters"], cleo_closed, cleo_direct)

for rs, ss in [
    ("0.2", "0.6"), ("1", "0.5"), ("-1", "0.5"),
    ("1", "1"), ("-1", "1"), ("0", "1"),
    ("-0.6", "-0.6"), ("0.999999", "0.9999999"),
]:
    r, s = mp.mpf(rs), mp.mpf(ss)
    record("inverse_hyperbolic_companion", [rs, ss], L_atanh(r, s), L_atanh_quad(r, s))

for ps, qs, theta_s in [("1", "2", "0.4"), ("-2", "1", "1.4"), ("0.2", "3", "2.6")]:
    p, q, theta = map(mp.mpf, (ps, qs, theta_s))
    direct = mp.quad(lambda x: mp.atan(p * mp.sin(x)) * mp.atan(q * mp.sin(x)) / mp.sin(x), [0, theta])
    record("ordinary_primitive", [ps, qs, theta_s], I_classical(p, q, mp.tan(theta / 2)), direct)

for ps, qs in [("1", "2"), ("-2", "1"), ("1", "1"), ("1", "-1"), ("0", "0"), ("0", "0.7")]:
    p, q = mp.mpf(ps), mp.mpf(qs)
    direct = mp.quad(lambda x: mp.sin(x) / ((1 + p * p * mp.sin(x) ** 2) * (1 + q * q * mp.sin(x) ** 2)), [0, mp.pi / 2])
    record("elementary_mixed_derivative", [ps, qs], elementary_mixed(p, q), direct)
    alpha, beta = mp.asinh(p), mp.asinh(q)
    closed = (sinh_quotient(alpha + beta) + sinh_quotient(alpha - beta)) / 2
    record("hyperbolic_mixed_derivative", [ps, qs], closed, mp.cosh(alpha) * mp.cosh(beta) * direct)

for m in range(1, 7):
    for A, B, sign in [("0.2", "0.3", 1), ("0.2", "0.3", -1), ("0.25", "0.25", 1)]:
        a, b = mp.j * mp.mpf(A), mp.j * sign * mp.mpf(B)
        record("higher_logarithmic_order", [m, A, B, sign], L_series(a, b, m), L_quad(a, b, m))

for m in (1, 2, 4, 6):
    p, q, T = mp.mpf("0.2"), mp.mpf("0.6"), mp.mpf("0.1")
    record("Euler_ladder", [m, "0.2", "0.6", "0.1"], I_series(p, q, T, m), I_quad(p, q, T, m))

for m in (1, 2, 4, 6):
    A = mp.mpf("0.25")
    closed = 2 ** (-m - 1) * Li_r1_series(m + 1, -A * A, 1) - 2 * mp.re(Li_r1_series(m + 1, mp.j * A, 1))
    direct = mp.quad(lambda t: (-mp.log(t)) ** (m - 1) * mp.atan(A * t) ** 2 / t, [0, 1]) / mp.factorial(m - 1)
    record("diagonal_double_polylog", [m, "0.25"], closed, direct)

result = {
    "precision_decimal_digits": mp.mp.dps,
    "exact_checks": exact,
    "numeric_check_count": len(records),
    "maximum_absolute_error": mp.nstr(max(mp.mpf(r["absolute_error"]) for r in records), 12),
    "status": "all checks passed; numeric comparisons are audits, not proofs",
    "records": records,
}
OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "records"}, indent=2))
