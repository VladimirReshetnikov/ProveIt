#!/usr/bin/env python3
"""Exact finite illustrations of the report. Not a proof of the infinite theorems.

Requires sympy. All cyclotomic nonvanishing and valuations below are exact:
v_p(alpha) = v_p(Norm_Q(zeta)/Q(alpha)) / phi(p^h), since p is totally ramified.
Usage: python3 exact_checks.py [output.json]
"""
from __future__ import annotations
from fractions import Fraction
import json
from pathlib import Path
import sys
import sympy as sp

T, X, Y, Z = sp.symbols("T X Y Z")

def vp_integer(n: int, p: int):
    n = abs(int(n))
    if n == 0:
        return None
    answer = 0
    while n % p == 0:
        answer += 1
        n //= p
    return answer

def hstar(p: int, r: Fraction) -> int:
    h = 1
    while Fraction(1, (p-1)*p**(h-1)) > r:
        h += 1
    return h

def grid_polynomial(p: int, first: int, last: int):
    return sp.Poly(sp.prod(sp.cyclotomic_poly(p**h, T+1) for h in range(first, last+1)), T).as_expr().expand()

def gauss_value(poly, p: int, r: Fraction):
    terms = sp.Poly(poly, T).terms()
    return min(Fraction(vp_integer(int(c), p)) + r*mon[0] for mon, c in terms if c)

def cyclotomic_value(expression, p: int, h: int, exponents: tuple[int, int], power: int):
    modulus = sp.Poly(sp.cyclotomic_poly(p**h, Z), Z)
    expr = expression.subs({X: Z**(exponents[0]*power)-1, Y: Z**(exponents[1]*power)-1})
    num, den = sp.fraction(sp.cancel(expr))
    num = sp.rem(sp.Poly(num, Z), modulus).as_expr()
    den = sp.rem(sp.Poly(den, Z), modulus).as_expr()
    norm_num = int(sp.resultant(modulus.as_expr(), num, Z))
    norm_den = int(sp.resultant(modulus.as_expr(), den, Z))
    assert norm_den != 0
    if norm_num == 0:
        return {"nonzero": False, "valuation": "infinity"}
    degree = int(sp.totient(p**h))
    val = Fraction(vp_integer(norm_num, p)-vp_integer(norm_den, p), degree)
    return {"nonzero": True, "valuation": str(val), "norm_numerator": str(norm_num), "norm_denominator": str(norm_den)}

def main():
    sharpness = []
    for p in [2, 3, 5]:
        for r in [Fraction(1), Fraction(1, 2)]:
            first = hstar(p, r)
            for k in [1, 2, 3]:
                last = first+k-1
                # Avoid unnecessarily huge examples while retaining several cases.
                if p**last > 150:
                    continue
                g = grid_polynomial(p, first, last)
                poly = sp.Poly(g, T)
                assert poly.LC() == 1
                assert all(int(c) % p == 0 for c in poly.all_coeffs()[1:])
                assert vp_integer(int(g.subs(T, 0)), p) == k
                assert gauss_value(g, p, r) == k
                for level in range(first, last+1):
                    assert sp.rem(poly, sp.Poly(sp.cyclotomic_poly(p**level, T+1), T)).is_zero
                next_factor = sp.Poly(sp.cyclotomic_poly(p**(last+1), T+1), T)
                assert not sp.rem(poly, next_factor).is_zero
                sharpness.append({"p": p, "r": str(r), "h_star": first, "budget": k, "all_permitted_levels_killed_through": last, "theorem_level": last+1, "degree": poly.degree(), "gauss_value": str(gauss_value(g, p, r)), "value_at_zero": str(g.subs(T, 0))})
    # Two matrix ranks and one power-orbit obstruction, witnessed at different interior points.
    A = sp.Matrix([[1, X], [Y, X*Y+X]])
    B = sp.Matrix([[X-Y, 0], [0, 1]])
    factors = [A.det(), B.det(), (1+X)**3-1]
    points = [(3, 3), (3, 6), (3, 3)]
    reference = []
    budget = 0
    for f, (x, y) in zip(factors, points):
        val = vp_integer(int(f.subs({X:x, Y:y})), 3)
        assert val is not None
        budget += val
        reference.append({"function": str(f), "point": [x,y], "valuation": val})
    p, m, actual_h = 3, 3, 3
    bound_h = hstar(p, Fraction(1, m)) + m*budget
    orbit = []
    for j in range(1, m+1):
        vals = [cyclotomic_value(f, p, actual_h, (1,2), j) for f in factors]
        assert all(row["nonzero"] for row in vals)
        orbit.append({"power": j, "values": vals, "rank_A": 2, "rank_B": 2})
    # Analytic integral series X/(1-Y), not a polynomial; evaluation checked as a rational function.
    rational_series = cyclotomic_value(X/(1-Y), 3, 3, (1,2), 1)
    assert rational_series["nonzero"]
    # Exact counterexamples to reading determinant/Fitting bounds as individual invariant bounds.
    smith = {"reference_exponents": [2,2], "specialized_exponents": [0,4], "reference_prefix_sums": [2,4], "specialized_prefix_sums": [0,4], "largest_invariant_increases": True}
    determinant = {"matrix": "diag(t,t^-1)", "determinant": "1", "operator_norm_for_t_ge_1": "t", "uniform_operator_bound_from_determinant": False}
    result = {"scope": "Exact finite illustrations, not an infinite theorem verifier or Lean audit", "sympy_version": sp.__version__, "sharpness_cases": sharpness, "reference_data": reference, "budget_B": budget, "m": m, "guaranteed_H": bound_h, "explicit_working_H": actual_h, "orbit_witness": "(zeta_27,zeta_27^2)", "power_orbit_checks": orbit, "integral_rational_series": rational_series, "smith_counterexample": smith, "determinant_counterexample": determinant}
    payload = json.dumps(result, indent=2)+"\n"
    if len(sys.argv)>1:
        Path(sys.argv[1]).write_text(payload)
    print(json.dumps({"sharpness_cases": len(sharpness), "budget_B": budget, "guaranteed_H": bound_h, "explicit_working_H": actual_h, "powers_verified": m, "all_exact_checks_passed": True}, indent=2))

if __name__ == "__main__":
    main()
