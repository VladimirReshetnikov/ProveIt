#!/usr/bin/env python3
"""Independent exact checks of the Gamma-sector theorem and endpoints.

The complete normal form is computed by integration by parts in a free
differential algebra.  Its coefficients are then compared with the
separately implemented variational rational recurrence.  All assertions
are exact; these finite checks supplement, and do not replace, the proof.
"""
import json
from collections import Counter
from fractions import Fraction
from math import factorial
from pathlib import Path
import sympy as sp
from gamma_normal_form import (add, derivative, functional, normal_form,
                               gamma_successor, serialize)

DATA = Path(__file__).resolve().parent.parent / "data"
DATA.mkdir(exist_ok=True)
X = sp.Symbol("X")
ratios = {0: -1 / ((X - 1) * (X + 1)), 1: sp.Integer(0)}
numerators = {}
polynomial_checks = 0
for n in range(1, 10):
    moment = sum(sp.binomial(n, j) * 3**j / (X + 2*j + 3)
                 for j in range(n + 1)) / (sp.factorial(n) * 24**n)
    ratios[n + 1] = sp.factor((moment - (n + 1 + (2*n - 1)*(X + 2))
                              * ratios[n].subs(X, X + 2)
                              - sp.Rational(n - 2, 4)*ratios[n - 1].subs(X, X + 4))
                             / (4*(n + 1)*(X + 1)*(X + 2)))
    b = n + 1
    numerator = sp.cancel(ratios[b] * sp.prod(X + 2*j + 1 for j in range(b + 1)))
    polynomial = sp.Poly(numerator, X, domain=sp.QQ)
    assert polynomial.degree() == b - 2
    assert polynomial.LC() == 1 / (4*sp.factorial(b)*6**(b - 1))
    numerators[b] = polynomial.as_expr()
    polynomial_checks += 1

polynomial_records = {}
normal_forms = {}
full_identity_checks = 0
sector_checks = 0
gamma_polynomial = {(): Fraction(1)}
for weight in range(25):
    normal, primitive = normal_form(gamma_polynomial)
    assert add(normal, derivative(primitive)) == gamma_polynomial
    assert all(functional(m) for m in normal)
    assert all(sum(r + 1 for r in m) == weight for m in normal)
    assert all(sum(r + 1 for r in m) == weight - 1 for m in primitive)
    full_identity_checks += 1
    for b in range(weight // 3 + 1):
        for k in range((weight - 3*b) // 2 + 1):
            a = weight - 3*b - 2*k
            monomial = (0,)*a + (1,)*k + (2,)*b
            actual = normal.get(monomial, Fraction(0))
            if k % 2 or b == 1:
                expected = sp.Integer(0)
            else:
                expected = (sp.factorial(weight) / (sp.factorial(a)*2**k*sp.factorial(k))
                            * ratios[b].subs(X, k))
            assert sp.Rational(actual.numerator, actual.denominator) == expected, (weight, a, k, b)
            sector_checks += 1
    if weight <= 14:
        polynomial_records[str(weight)] = {"normal": serialize(normal),
                                           "primitive": serialize(primitive)}
        normal_forms[weight] = (normal, primitive)
    gamma_polynomial = gamma_successor(gamma_polynomial)

# Verify the closed square/cube functions against the entire power series.
y = sp.Symbol("y")
f2 = ((y*y + 3)*sp.sinh(y) - 3*y*sp.cosh(y)) / (48*y**5)
f3 = ((2*y**4 + 60*y*y + 135)*sp.sinh(y)
      - 15*y*(y*y + 9)*sp.cosh(y)) / (1728*y**7)
closed_series_checks = 0
for b, expression in [(2, f2), (3, f3)]:
    expansion = sp.series(expression, y, 0, 20).removeO().expand()
    for k in range(20):
        expected = 0 if k % 2 else ratios[b].subs(X, k) / sp.factorial(k)
        assert expansion.coeff(y, k) == expected
        closed_series_checks += 1

# Local endpoint evaluation uses truncated Laurent series, independent of
# the variational recurrence.  Zeta values remain algebraically formal.
gamma = sp.Symbol("gamma")
zeta = {n: sp.Symbol("zeta_" + str(n)) for n in range(2, 16)}

def multiply_series(left, right, maximum):
    result = {}
    for i, value in left.items():
        for j, coefficient in right.items():
            if i + j <= maximum:
                result[i+j] = result.get(i+j, 0) + value * coefficient
    return {i: sp.expand(c) for i, c in result.items() if c != 0}


def endpoint_monomial(monomial):
    weight = sum(r+1 for r in monomial)
    series = {0: sp.Integer(1)}
    at_one = sp.Integer(1)
    for r in monomial:
        normalized = {0: (-1)**(r+1)*sp.factorial(r)}
        if r == 0:
            normalized[1] = -gamma
            at_one *= -gamma
        else:
            at_one *= (-1)**(r+1)*sp.factorial(r)*zeta[r+1]
        for j in range(max(r, 1), weight):
            normalized[j+1] = ((-1)**(j+1)*zeta[j+1]
                               * sp.factorial(j)/sp.factorial(j-r))
        series = multiply_series(series, normalized, weight)
    return sp.expand(at_one - series.get(weight, 0))

endpoints = {}
for weight in (9, 10):
    primitive = normal_forms[weight][1]
    value = sp.expand(sum(sp.Rational(c.numerator, c.denominator)*endpoint_monomial(m)
                          for m, c in primitive.items()))
    endpoints[weight] = value

Z2, Z3, Z4, Z5, Z6, Z7, Z8 = [zeta[n] for n in range(2, 9)]
printed_B9 = (-252*gamma**6*Z2 + 1260*gamma**5*Z3
              + gamma**4*(3150*Z2**2 - 5670*Z4)
              + gamma**3*(-17640*Z2*Z3 + 20328*Z5)
              + gamma**2*(-7560*Z2**3 + 40572*Z2*Z4 + 16884*Z3**2 - 57456*Z6)
              + gamma*(28476*Z2**2*Z3 - 70560*Z2*Z5 - 54432*Z3*Z4 + 106416*Z7)
              + 1932*Z2**4 - 22050*Z2**2*Z4 - 18648*Z2*Z3**2 + 63036*Z2*Z6
              + 47376*Z3*Z5 + 21942*Z4**2 - 99624*Z8)
assert sp.expand(endpoints[9] - printed_B9) == 0
# Appell translation is an independent consistency check on the endpoint.
assert sp.expand(sp.diff(endpoints[10], gamma) + 10*endpoints[9]) == 0

record = {
    "all_passed": True,
    "arithmetic": "exact Fraction and SymPy rational/symbolic arithmetic",
    "complete_normal_form_identities": full_identity_checks,
    "maximum_weight": 24,
    "sector_coefficient_checks": sector_checks,
    "polynomial_numerator_checks": polynomial_checks,
    "closed_function_series_checks": closed_series_checks,
    "endpoint_checks": 2,
    "total_checks": full_identity_checks + sector_checks + polynomial_checks + closed_series_checks + 2,
    "scope": "Finite exact checks; all-order validity is proved in the article."
}
(DATA / "gamma_verification.json").write_text(json.dumps(record, indent=2) + "\n")
(DATA / "gamma_normal_forms.json").write_text(json.dumps(polynomial_records, indent=2) + "\n")
(DATA / "gamma_sector_numerators.json").write_text(json.dumps(
    {str(b): {"p_b": str(p), "r_b": str(ratios[b]), "p_b_latex": sp.latex(p)}
     for b, p in numerators.items()}, indent=2) + "\n")
(DATA / "gamma_endpoints.json").write_text(json.dumps(
    {str(w): {"expression": str(v), "latex": sp.latex(v)} for w, v in endpoints.items()},
    indent=2) + "\n")
print(json.dumps(record, indent=2))
