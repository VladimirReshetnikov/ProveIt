#!/usr/bin/env python3
"""Verify the polynomial certificates in article.tex using exact symbolic arithmetic.

This is the SymPy half of the package's two independent certificate checkers.
The other half, ../certificates.py, verifies the same identities with its own
exact rational polynomial arithmetic and no computer algebra system; keeping
both means no single implementation or CAS version is the sole witness.
This script also checks the bivariate identity (4.12) of the article in one
piece, whereas the CAS-free script certifies it through its three
coefficientwise components.

The notation follows the merged article: A_d, H_d and B for the quadratic-form
coefficients, M_d for the cycle mixed term, L_d for the k-substituted lower
bound, and alpha, beta, gamma for the three fifth-order auxiliaries.

No row enumeration, numerical optimization, or floating-point arithmetic is used.
Run from the archive root: python code/verify_certificates.py
"""
from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path
import sympy as sp


def verify() -> dict:
    t, k, u, v, w, z = sp.symbols("t k u v w z")
    a, am, ap, b, bm, bp = sp.symbols("a am ap b bm bp")
    passed: list[str] = []

    def identity(name: str, lhs: sp.Expr, rhs: sp.Expr = sp.S.Zero) -> None:
        difference = sp.cancel(sp.expand(lhs - rhs))
        if difference != 0:
            raise AssertionError(f"{name}: nonzero difference {difference}")
        passed.append(name)

    # The universal slack decomposition of the article's Lemma 3.2.
    A, B, H = a*a-am*ap, b*b-bm*bp, 2*a*b-am*bp-ap*bm
    direct = (a*u+b*v)**2-(am*w+bm*u)*(ap*v+bp*z)
    decomposed = (am*ap*(u*u-w*v) + bm*bp*(v*v-u*z)
                  + am*bp*(u*v-w*z) + A*u*u + H*u*v + B*v*v)
    identity("universal four-term defect decomposition", direct, decomposed)

    y = sp.symbols("y")
    expected_H = [sp.S.Zero, sp.Integer(2), 4*(-2*k+2*t-1),
                  6*(-9*k*t+9*k+3*t*t-6*t+11)]
    expected_A = [sp.S.Zero, sp.S.One, 4*(2*t*t-2*t-3),
                  9*(3*t**4-12*t**3-9*t*t+42*t+40)]
    for d in range(4):
        P = sp.sympify(sp.prod(t-j for j in range(d)))
        Pm, Pp = P.subs(t, t-d), P.subs(t, t+d)
        identity(f"order {d+1} A_{d} expansion", P*P-Pm*Pp, expected_A[d])
        identity(f"order {d+1} H_{d} expansion", 2*P*k-Pm*(k+1)-Pp*(k-1),
                 expected_H[d])
    identity("order 3 boundary lower bound L_2",
             expected_H[2].subs(k, t/3), 4*(4*t/3-1))
    identity("order 4 boundary lower bound L_3",
             expected_H[3].subs(k, t/4), sp.Rational(3, 2)*(3*t*t-15*t+44))

    P4 = t*(t-1)*(t-2)*(t-3)
    Pm, Pp = P4.subs(t, t-4), P4.subs(t, t+4)
    A4 = sp.expand(P4*P4-Pm*Pp)
    H4 = sp.expand(2*P4*k-Pm*(k+1)-Pp*(k-1))
    alpha = 2*t**3+9*t*t-161*t+255
    beta = 2*t*t-6*t+9
    gamma = 7*t**3-31*t*t-126*t+1080
    L4 = -sp.Rational(16, 5)*alpha
    identity("order 5 A_4 expansion", A4,
             32*(2*t**6-18*t**5+17*t**4+168*t**3-55*t*t-834*t-630))
    identity("order 5 H_4 expansion", H4,
             16*(-12*k*t*t+36*k*t-54*k+2*t**3-9*t*t+43*t-51))
    identity("order 5 mixed-term remainder H_4 - L_4", H4-L4,
             sp.Rational(96, 5)*beta*(t-5*k))
    identity("order 5 discriminant factorization 4A_4 - L_4^2", 4*A4-L4*L4,
             sp.Rational(384, 25)*(t-5)*beta*gamma)
    identity("order 5 integer square certificate", 25*(A4*u*u+H4*u*v+v*v),
             (5*v-8*alpha*u)**2+96*(t-5)*beta*gamma*u*u+480*beta*(t-5*k)*u*v)
    identity("positive quadratic beta", beta,
             2*(t-sp.Rational(3, 2))**2+sp.Rational(9, 2))
    identity("positive shifted cubic gamma", gamma.subs(t, y+10),
             7*y**3+179*y*y+1354*y+3720)
    if not all(c > 0 for c in sp.Poly(gamma.subs(t, y+10), y).all_coeffs()):
        raise AssertionError("shifted cubic has a nonpositive coefficient")
    passed.append("all shifted cubic coefficients strictly positive")

    M4 = sp.expand(2*P4*t-Pm*(t+4)-Pp*(t-4))
    identity("cycle mixed term M_4", M4, -32*(t-2)*(2*t*t+4*t-51))
    identity("cycle obstruction factorization 64A_4 - M_4^2", 64*A4-M4**2,
             -9216*(t-4)*(t+4)*(2*t-9)*beta)

    r, s = sp.symbols("r s")
    numerator = 3*(3*r+1)*(3*r+2)*(r+2)**2
    denominator = 4*(r+1)**2*(2*r+3)**2
    difference = 11*r**4+55*r**3+74*r*r+12*r-12
    identity("sharpness ratio difference", numerator-denominator, difference)
    identity("sharpness positive shifted polynomial", difference.subs(r, s+1),
             11*s**4+99*s**3+305*s*s+369*s+140)
    if not all(c > 0 for c in sp.Poly(difference.subs(r, s+1), s).all_coeffs()):
        raise AssertionError("sharpness shifted polynomial has a nonpositive coefficient")
    passed.append("all sharpness shifted polynomial coefficients strictly positive")
    return {
        "status": "PASS",
        "arithmetic": "exact symbolic rational polynomial arithmetic",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "checks_passed": len(passed),
        "checks": passed,
        "companion_cas_free_checker": "certificates.py, run separately",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional path for a JSON report")
    args = parser.parse_args()
    report = verify()
    text = json.dumps(report, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+"\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
