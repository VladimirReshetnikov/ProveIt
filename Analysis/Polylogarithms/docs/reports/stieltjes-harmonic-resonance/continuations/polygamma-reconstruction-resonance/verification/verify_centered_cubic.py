#!/usr/bin/env python3
"""Independent exact and numerical checks for centered cubic trigamma moments.

All files written by this script are diagnostics.  The analytic proof is in
centered_cubic_trigamma.tex; numerical residuals are not interval certificates.
"""
from __future__ import annotations

import json
import math
from pathlib import Path
from functools import lru_cache

import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
N, t, z = sp.symbols("N t z")
Z2, Z3, Z4, Z5, Z6, gamma = sp.symbols("zeta2 zeta3 zeta4 zeta5 zeta6 gamma")


def B(n):
    return sp.bernoulli(n, 0)


def BC(n):
    return sp.bernoulli(n, sp.Rational(1, 2))


@lru_cache(None)
def tail_coefficient(power, exponent):
    """Coefficient of N^-exponent in the ordinary expansion of A_N^power."""
    if power == 0:
        return sp.Integer(exponent == 0)
    return sum(B(k - 1) * tail_coefficient(power - 1, exponent - k)
               for k in range(1, exponent + 1))


def boundary_ct(poly, power):
    poly = sp.Poly(sp.expand(poly), N)
    return sp.expand(sum(c * tail_coefficient(power, a[0])
                         for a, c in poly.terms()))


def faulhaber(m):
    return sp.expand((sp.bernoulli(m + 1, N + 1) - sp.bernoulli(m + 1, 1)) / (m + 1))


@lru_cache(None)
def cutoff_ct(power, exponent):
    """Exact finite-summation recursion, independent of the asserted C_j formula."""
    if power == 0:
        if exponent >= 0:
            return sp.Integer(0)
        return {-1: gamma, -2: Z2, -3: Z3, -4: Z4}[exponent]
    if power == 1 and exponent == -1:
        return Z3  # zeta(2,1)
    if power == 1 and exponent == -2:
        return sp.Rational(3, 4) * Z4  # zeta(2,2)
    if exponent < 0:
        raise ValueError((power, exponent))
    F = faulhaber(exponent)
    out = boundary_ct(F, power)
    for (a,), coefficient in sp.Poly(F.subs(N, N - 1), N).terms():
        for h in range(1, power + 1):
            out += sp.binomial(power, h) * coefficient * cutoff_ct(power - h, a - 2*h)
    return sp.expand(out)


def C_by_cutoff(j):
    return sp.expand(3*cutoff_ct(2, 2*j - 2)
                     + 3*cutoff_ct(1, 2*j - 4)
                     + cutoff_ct(0, 2*j - 6)
                     + tail_coefficient(3, 2*j))


@lru_cache(None)
def C_formula(j):
    out = 9*B(2*j - 2)*Z3
    if j == 1:
        return out - sp.Rational(17, 4)*Z4
    out -= sp.Rational(3, 2*(2*j - 1))*sum(
        (2*h + 1)*sp.binomial(2*j - 1, 2*h + 3)*B(2*j - 4 - 2*h)*B(2*h)
        for h in range(j - 1))
    if j == 2:
        out -= Z2/2
    if j == 3:
        out += sp.Rational(1, 4)
    return sp.expand(out)


@lru_cache(None)
def moment(r):
    return sp.expand(sum(sp.binomial(2*r + 2, 2*j)*BC(2*r + 2 - 2*j)*C_formula(j)
                         / (2*r + 2) for j in range(1, r + 2)))


@lru_cache(None)
def square_moment(r):
    return sp.expand(3*BC(2*r)*Z3 - sp.Rational(1, 2)*sum(
        sp.binomial(2*r, 2*j)*sp.Rational(2*j - 1, 2*j + 1)
        * BC(2*r - 2*j)*B(2*j - 2) for j in range(1, r + 1)))


def C_from_generator(j):
    out = 3*sum(sp.binomial(2*j - 2, 2*k)*sp.Rational(1, 2)**(2*j - 2 - 2*k)
                * square_moment(k) for k in range(j))
    out -= sp.Rational(17, 4)*Z4 if j == 1 else 0
    out -= Z2/2 if j == 2 else 0
    out += sp.Rational(1, 4) if j == 3 else 0
    return sp.expand(out)


@lru_cache(None)
def centered_cube_coeff(k):
    return sum(BC(2*a)*BC(2*b)*BC(2*(k-a-b))
               for a in range(k+1) for b in range(k-a+1))


def cube_polylog_formula():
    # Symbol labels stand for Li_a(exp(-t)) and Li_{a,b}(exp(-t)).
    L = {a: sp.Symbol(f"L{a}") for a in range(1, 7)}
    M = {(a, b): sp.Symbol(f"M{a}_{b}") for a in range(1, 5) for b in range(2, 5)}
    C = ((9*Z4 + 6*t*Z3 - t**4/16)*L[2]
         + (12*Z3 - t**3/2)*L[3] - 3*t**2*L[4] - 12*t*L[5]
         - sp.Rational(45, 2)*L[6] - sp.Rational(3, 2)*t**2*M[2,2]
         - 6*t*(M[3,2] + M[2,3]) - 9*(M[4,2] + M[2,4]) - 12*M[3,3]
         + sp.Rational(15, 2)*Z6 - 6*Z3**2 + 6*t*Z5 + Z3*t**3/2
         + Z4*t**2/8 - Z2*t**4/48 - t**6/1440)
    def D(expr):
        result = sp.diff(expr, t) - z*sp.diff(expr, z)
        for a, symbol in L.items():
            derivative = -L[a-1] if a > 1 else -z/(1-z)
            result += sp.diff(expr, symbol)*derivative
        for (a,b), symbol in M.items():
            derivative = -M[a-1,b] if a > 1 else -z*L[b]/(1-z)
            result += sp.diff(expr, symbol)*derivative
        return sp.expand(result)
    coth = (1+z)/(1-z)
    square_times_cosh = t*coth/2*(2*Z3-t**3/48-t*L[2]/2-2*L[3]
                                                 + 3*(Z4-L[4])/t)
    rhs = 3*square_times_cosh-sp.Rational(17,4)*Z4-Z2*t**2/4+t**4/96
    check = sp.factor(D(D(C))-rhs)
    assert check == 0, check
    return C, L, M


def mpq(q):
    q = sp.Rational(q)
    return mp.mpf(int(q.p))/int(q.q)


def exact_to_mp(expr):
    return mp.mpf(str(expr.subs({Z2: sp.zeta(2), Z3: sp.zeta(3), Z4: sp.zeta(4),
                                Z5: sp.zeta(5), Z6: sp.zeta(6)}).evalf(mp.mp.dps)))


def numeric_moment(r, cutoff, asymptotic_terms):
    coeff = [mpq(centered_cube_coeff(k)) for k in range(asymptotic_terms+1)]
    total = mp.mpf(0)
    for n in range(cutoff):
        x = mp.mpf(n)+mp.mpf("0.5")
        value = x**(2*r+1)*mp.polygamma(1, n+1)**3
        value -= sum(coeff[k]*x**(2*r-2-2*k) for k in range(r))
        total += value
    for k in range(r, asymptotic_terms+1):
        total += coeff[k]*mp.zeta(2*(k-r+1), mp.mpf(cutoff)+mp.mpf("0.5"))
    return total


def multiple_li(a, b, x):
    total = mp.mpf(0)
    harmonic = mp.mpf(0)
    xpower = x
    cutoff = int(mp.ceil((mp.mp.dps+12)*mp.log(10)/(-mp.log(x))))+10
    for n in range(1, cutoff+1):
        total += xpower*harmonic/n**a
        harmonic += mp.mpf(1)/n**b
        xpower *= x
    return total


def main():
    exact = {"cutoff_vs_bernoulli": [], "generator_vs_bernoulli": [], "moment_table": []}
    for j in range(1, 19):
        assert sp.expand(C_by_cutoff(j)-C_formula(j)) == 0
        exact["cutoff_vs_bernoulli"].append(j)
        assert sp.expand(C_from_generator(j)-C_formula(j)) == 0
        exact["generator_vs_bernoulli"].append(j)
    for r in range(12):
        exact["moment_table"].append({"r": r, "value": str(moment(r)),
                                      "subtractions": [str(centered_cube_coeff(k)) for k in range(r)]})
    coordinates = (Z2, Z3, Z4)
    matrix = sp.Matrix([[moment(r).coeff(c) for c in coordinates]
                        + [moment(r).subs({c: 0 for c in coordinates})] for r in range(4)])
    assert matrix.det() == sp.Rational(51, 81920)
    assert sp.expand(sum(a*moment(r) for r,a in enumerate([11,198,512,224]))) == -sp.Rational(21,2)
    exact["first_four_coordinate_determinant"] = str(matrix.det())
    exact["first_four_inverse"] = [[str(v) for v in matrix.inv().row(i)] for i in range(4)]
    exact["rational_cubic_identity"] = "exact"
    zeta3_weights = [37, 2136, 11344, 7168]
    assert sp.expand(sum(a*moment(r) for r,a in enumerate(zeta3_weights))) == 252*Z3
    zeta3_subtraction = sp.expand(sum(
        a*sum(centered_cube_coeff(k)*t**(2*r-2-2*k) for k in range(r))
        for r,a in enumerate(zeta3_weights)))
    assert zeta3_subtraction == 7168*t**4+9552*t**2+sp.Rational(1148,15)
    exact["zeta3_cubic_extraction"] = {"weights": zeta3_weights, "value": "252*zeta3",
                                         "subtraction": str(zeta3_subtraction), "status": "exact"}
    formula, L, M = cube_polylog_formula()
    exact["polylog_second_derivative"] = "exact zero"
    mp.mp.dps = 110
    numeric = {"precision": mp.mp.dps, "method": "direct sum plus independently generated centered Hurwitz tail",
               "moments": [], "generator": []}
    for r in range(9):
        wanted = exact_to_mp(moment(r))
        v1 = numeric_moment(r, 160, 32)
        v2 = numeric_moment(r, 320, 36)
        numeric["moments"].append({"r": r, "expected": mp.nstr(wanted, 85),
                                  "residual_160_32": mp.nstr(abs(v1-wanted), 12),
                                  "residual_320_36": mp.nstr(abs(v2-wanted), 12),
                                  "successive_difference": mp.nstr(abs(v1-v2), 12)})
    for point in [mp.mpf("0.4"), mp.mpf("0.9"), mp.mpf("1.7")]:
        x = mp.exp(-point)
        replacements = {t: point, Z2: mp.zeta(2), Z3: mp.zeta(3), Z4: mp.zeta(4),
                        Z5: mp.zeta(5), Z6: mp.zeta(6)}
        replacements.update({symbol: mp.polylog(a,x) for a,symbol in L.items()})
        replacements.update({symbol: multiple_li(a,b,x) for (a,b),symbol in M.items()
                             if formula.has(symbol)})
        polylog_value = mp.mpf(str(formula.subs(replacements).evalf(100)))/(2*mp.sinh(point/2))
        # No polylogarithms enter this comparison value: only the finite moment formula.
        series_value = sum(exact_to_mp(moment(r))*point**(2*r+1)/mp.factorial(2*r+1)
                           for r in range(90))
        numeric["generator"].append({"t": str(point), "polylog": mp.nstr(polylog_value,70),
                                     "series_90_residual": mp.nstr(abs(polylog_value-series_value),12)})
    (HERE/"centered_cubic_exact.json").write_text(json.dumps(exact, indent=2)+"\n")
    (HERE/"centered_cubic_numeric.json").write_text(json.dumps(numeric, indent=2)+"\n")
    print(json.dumps({"exact_cutoff_checks": len(exact["cutoff_vs_bernoulli"]),
                      "exact_generator_checks": len(exact["generator_vs_bernoulli"]),
                      "exact_polylog_derivative": exact["polylog_second_derivative"],
                      "numerical_moments": numeric["moments"],
                      "numerical_generator": numeric["generator"]}, indent=2))


if __name__ == "__main__":
    main()
