#!/usr/bin/env python3
"""Exact finite checks for The Order-Three Threshold manuscript.

Python 3.9+, SymPy 1.13 or later. Run from any working directory:
    python code/verify.py

The infinite theorems are proved in article.tex. This script checks finite
algebraic identities and truncations only; it is not a formal proof checker.
"""
from __future__ import annotations

import itertools
import json
import math
import platform
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install the dependency with: python -m pip install sympy") from exc

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Dict[str, int] = {}
DETAILS: Dict[str, object] = {}


def check(group: str, condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {message}")
    COUNTS[group] = COUNTS.get(group, 0) + 1


@dataclass(frozen=True)
class QZ:
    """Sparse Q[z][q]/(q^cutoff), with exact rational coefficients."""

    cutoff: int
    terms: Dict[Tuple[int, int], Fraction]

    @staticmethod
    def scalar(cutoff: int, value: object) -> QZ:
        c = Fraction(value)
        return QZ(cutoff, {(0, 0): c} if c else {})

    @staticmethod
    def monomial(cutoff: int, q_degree: int, z_degree: int,
                 value: object = 1) -> QZ:
        if q_degree < 0 or z_degree < 0:
            raise ValueError("Only nonnegative polynomial exponents are supported")
        c = Fraction(value)
        return QZ(cutoff, {(q_degree, z_degree): c}
                  if c and q_degree < cutoff else {})

    def coerce(self, other: object) -> QZ:
        if isinstance(other, QZ):
            if other.cutoff != self.cutoff:
                raise ValueError("Incompatible q-adic cutoffs")
            return other
        return QZ.scalar(self.cutoff, other)

    def __add__(self, other: object) -> QZ:
        b = self.coerce(other)
        result = dict(self.terms)
        for key, value in b.terms.items():
            c = result.get(key, Fraction(0)) + value
            if c:
                result[key] = c
            else:
                result.pop(key, None)
        return QZ(self.cutoff, result)

    __radd__ = __add__

    def __neg__(self) -> QZ:
        return QZ(self.cutoff, {key: -value for key, value in self.terms.items()})

    def __sub__(self, other: object) -> QZ:
        return self + (-self.coerce(other))

    def __rsub__(self, other: object) -> QZ:
        return self.coerce(other) + (-self)

    def __mul__(self, other: object) -> QZ:
        b = self.coerce(other)
        result: Dict[Tuple[int, int], Fraction] = {}
        for (q1, z1), a in self.terms.items():
            for (q2, z2), c in b.terms.items():
                if q1 + q2 >= self.cutoff:
                    continue
                key = (q1 + q2, z1 + z2)
                value = result.get(key, Fraction(0)) + a * c
                if value:
                    result[key] = value
                else:
                    result.pop(key, None)
        return QZ(self.cutoff, result)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> QZ:
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Exponent must be a nonnegative integer")
        result = QZ.scalar(self.cutoff, 1)
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result

    def dz(self) -> QZ:
        return QZ(self.cutoff,
                  {(q, z - 1): c * z for (q, z), c in self.terms.items() if z})

    def coefficient_in_q(self, exponent: int) -> Dict[int, Fraction]:
        return {z: c for (q, z), c in self.terms.items() if q == exponent}


def polynomial_from_sympy(cutoff: int, poly: sp.Poly, q_degree: int = 0) -> QZ:
    return QZ(cutoff, {(q_degree, monomial[0]): Fraction(int(c.p), int(c.q))
                      for monomial, c in poly.terms() if q_degree < cutoff})


def check_symbolic_jets() -> None:
    z, U, V, W = sp.symbols("z U V W")
    y = sp.symbols("Y0:4")
    c, g2, g3 = sp.symbols("c g2 g3")
    H = (z*z - 4)*(y[0]*y[2] - y[1]**2) + z*y[0]*y[1]
    H1 = sp.diff(H, z) + sum(sp.diff(H, y[j])*y[j+1] for j in range(3))
    J = y[0]*H1 - 2*y[1]*H
    B = c*y[0]**2 - H
    P = sp.expand((z*z - 4)*J**2 - 4*B**3 + g2*B*y[0]**4 + g3*y[0]**6)
    check("symbolic_jets", sp.expand(P.coeff(y[3], 2)
          - (z*z - 4)**3*y[0]**4) == 0, "highest third-jet coefficient")
    e = sp.symbols("E0:4")
    substitutions = {y[0]: e[0], y[1]: e[1]/z,
                     y[2]: (e[2] - e[1])/z**2,
                     y[3]: (e[3] - 3*e[2] + 2*e[1])/z**3}
    transformed = sp.Poly(sp.expand(z**6 * P.subs(substitutions,
                                                   simultaneous=True)), z)
    check("symbolic_jets", transformed.degree() == 6, "largest exterior z degree")
    top = sp.expand(transformed.LC().subs({e[0]: 1, e[1]: U,
                    e[2]: U*U + V, e[3]: U**3 + 3*U*V + W}))
    expected = W*W - 4*(c - V)**3 + g2*(c - V) + g3
    check("symbolic_jets", sp.expand(top - expected) == 0,
          "logarithmic homogeneous expression")
    residue = sp.expand(top.subs({c: sp.Rational(1, 12),
                                 g2: sp.Rational(1, 12),
                                 g3: -sp.Rational(1, 216)}))
    check("symbolic_jets", residue == W*W - V*V + 4*V**3,
          "theta residue identity")
    G, m, s = sp.symbols("G m s")
    u = m + G*s/(1+s)
    v = G*s*sp.diff(u, s)
    w = G*s*sp.diff(v, s)
    check("symbolic_jets", sp.factor(w*w - v*v + 4*v**3
                                      - (G*G - 1)*v*v) == 0,
          "parameterized binomial gap identity")
    check("symbolic_jets", sp.factor(v - (u-m)*(m+G-u)) == 0,
          "second-order endpoint example")
    # Verify the cancellation-removal mechanism, not just nonzero monomial symbols.
    for multiplicity in range(5):
        base = y[0]*y[2] - (2*m+G)*y[0]*y[1] + m*(m+G)*y[0]**2
        hom = (y[0]*y[2] - y[1]**2)**multiplicity * base
        q = sp.expand(hom.subs({y[0]: 1, y[1]: U, y[2]: U*U+V}))
        expected = V**multiplicity * (V + (U-m)*(U-m-G))
        check("endpoint_cancellation", sp.expand(q - expected) == 0,
              f"removed V multiplicity {multiplicity}")
        R = sp.cancel(q / V**multiplicity)
        check("endpoint_cancellation", sp.expand(R.subs(V, 0)
              - (U-m)*(U-m-G)) == 0, "endpoint polynomial")
    DETAILS["theta_exterior_logarithmic_polynomial"] = str(residue)
    DETAILS["theta_gap_polynomial"] = "G**2 - 1"


def check_polynomial_classification() -> None:
    x = sp.Symbol("x")
    admitted = 0
    # All nonzero polynomials of degree at most four with coefficients -1,0,1.
    for coeffs in itertools.product((-1, 0, 1), repeat=5):
        support = [j for j, a in enumerate(coeffs) if a]
        if not support:
            continue
        f = sp.Poly(sum(a*x**j for j, a in enumerate(coeffs)), x, domain=sp.QQ)
        theta = lambda a: sp.Poly(x*a.diff().as_expr(), x, domain=sp.QQ)
        f1 = theta(f)
        A = f*theta(f1) - f1*f1
        B = f*theta(A) - 2*f1*A
        cleared = B*B - A*A*f*f + 4*A*A*A
        actual = cleared.is_zero
        expected = len(support) == 1 or (
            len(support) == 2 and support[1] - support[0] == 1)
        check("finite_initial_classification", actual == expected,
              f"classification for coefficients {coeffs}")
        admitted += int(actual)
    DETAILS["finite_initial_classification"] = {
        "degree_bound": 4, "coefficient_set": [-1, 0, 1],
        "nonzero_polynomials_tested": 242, "admitted": admitted,
        "note": "An exhaustive finite test, not the general classification proof."}


def chebyshev_polynomials(maximum: int) -> list:
    x = sp.Symbol("z")
    result = [sp.Poly(2, x, domain=sp.QQ), sp.Poly(x, x, domain=sp.QQ)]
    for n in range(1, maximum):
        result.append(sp.Poly(x*result[n].as_expr() - result[n-1].as_expr(),
                              x, domain=sp.QQ))
    return result


def check_chebyshev_and_newton() -> None:
    x, u = sp.symbols("z u")
    polys = chebyshev_polynomials(24)
    for n in range(1, 25):
        polynomial = polys[n].as_expr()
        check("chebyshev", sp.expand(polynomial.subs(x, u+1/u)
                                     - u**n - u**(-n)) == 0,
              f"descent n={n}")
        formula = sum((-1)**j * sp.Rational(n, n-j)
                      * sp.binomial(n-j, j)*x**(n-2*j)
                      for j in range(n//2+1))
        check("chebyshev", sp.expand(polynomial-formula) == 0,
              f"coefficient formula n={n}")
        check("chebyshev", polys[n].LC() == 1 and polys[n].degree() == n,
              f"monicity n={n}")
    for n in range(81):
        r = 2*n+1
        weighted = [j*j-j*r for j in range(2*n+5)]
        least = min(weighted)
        indices = [j for j, a in enumerate(weighted) if a == least]
        check("newton_corners", indices == [n, n+1], f"active degrees n={n}")
        check("newton_corners", least == -n*(n+1), f"minimum n={n}")
    for p in (2, 3, 5, 7, 11):
        expression = sum(x**(p*n) for n in range(1, 12))
        check("positive_characteristic", sp.Poly(sp.diff(expression, x), x,
              modulus=p).is_zero, f"Frobenius derivative for p={p}")


def check_theta_truncation(cutoff: int = 48) -> None:
    # Terms q^N and higher are discarded. Differentiation is only in z,
    # so omitted high q terms cannot contribute to any checked coefficient.
    z = QZ.monomial(cutoff, 0, 1)
    q = lambda n: QZ.monomial(cutoff, n, 0)
    one = QZ.scalar(cutoff, 1)
    polynomials = chebyshev_polynomials(math.isqrt(cutoff-1))
    f = one
    for n in range(1, len(polynomials)):
        f = f + polynomial_from_sympy(cutoff, polynomials[n], n*n)
    product = one
    for m in range(1, (cutoff+1)//2 + 1):
        product = product*(one-q(2*m))*(one+q(2*m-1)*z+q(4*m-2))
    for exponent in range(cutoff):
        check("theta_product_truncation",
              f.coefficient_in_q(exponent) == product.coefficient_in_q(exponent),
              f"Jacobi product coefficient q^{exponent}")
    def lambert(r: int) -> QZ:
        return sum((q(2*n)*sum(d**r for d in range(1, n+1) if n % d == 0)
                    for n in range(1, (cutoff-1)//2+1)), QZ.scalar(cutoff, 0))
    c = Fraction(1, 12) - 2*lambert(1)
    g2 = Fraction(1, 12) + 20*lambert(3)
    g3 = -Fraction(1, 216) + Fraction(7, 3)*lambert(5)
    df = f.dz()
    H = (z*z-4)*(f*df.dz()-df*df)+z*f*df
    J = f*H.dz()-2*df*H
    B = c*f*f-H
    residual = (z*z-4)*J*J - 4*B**3 + g2*B*f**4 + g3*f**6
    for exponent in range(cutoff):
        check("theta_ode_truncation", not residual.coefficient_in_q(exponent),
              f"cleared ODE coefficient q^{exponent}")
    # Leading q-coefficients of the Taylor coefficients visible in this truncation.
    for m in range(math.isqrt(cutoff-1)+1):
        terms = [(q_degree, a) for (q_degree, z_degree), a in f.terms.items()
                 if z_degree == m]
        check("theta_coefficient_values", min(terms) == (m*m, Fraction(1)),
              f"leading Taylor coefficient at z^{m}")
    DETAILS["theta_qadic_check"] = {
        "cutoff_exclusive": cutoff,
        "all_coefficients_q_0_through": cutoff-1,
        "coefficient_ring": "Q[z]",
        "identities": ["Jacobi product after Chebyshev descent", "cleared third-order ODE"],
        "theta_terms": len(polynomials)-1,
        "remaining_residual_terms": len(residual.terms)}


def main() -> None:
    started = time.perf_counter()
    check_symbolic_jets()
    check_polynomial_classification()
    check_chebyshev_and_newton()
    check_theta_truncation()
    result = {
        "status": "passed",
        "scope": "Finite exact algebra only; not a formal verification of infinite theorems.",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "counts": COUNTS,
        "total_checks": sum(COUNTS.values()),
        "details": DETAILS,
        "elapsed_seconds": round(time.perf_counter()-started, 3)}
    destination = ROOT / "data" / "verification.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        raise
