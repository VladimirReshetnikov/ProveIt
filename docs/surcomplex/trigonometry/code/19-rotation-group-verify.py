#!/usr/bin/env python3
"""Exact finite checks accompanying 'Rotations of the Surreal Plane'.

Requires Python 3.9+ and SymPy. This does NOT construct surreal numbers,
check arbitrary Hahn summability, or verify the article in a proof assistant.
All checks are finite polynomial, rational, or truncated-series identities.
Run: python verify.py
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import List, Tuple

import sympy as sp

RESULTS: List[dict] = []


def check(name: str, expression: sp.Expr) -> None:
    """Assert that a finite symbolic rational expression is identically zero."""
    residual = sp.cancel(sp.expand(expression))
    if residual != 0:
        raise AssertionError(f"{name}: nonzero residual {residual}")
    RESULTS.append({"name": name, "passed": True})


def check_matrix(name: str, matrix: sp.Matrix) -> None:
    for j, expression in enumerate(matrix):
        check(f"{name}, entry {j + 1}", expression)


def cayley(t: sp.Expr) -> sp.Expr:
    return (1 + sp.I * t) / (1 - sp.I * t)


def homogeneous(s: sp.Expr, t: sp.Expr) -> sp.Expr:
    return (s * s - t * t + 2 * sp.I * s * t) / (s * s + t * t)


def product(u: Tuple[sp.Expr, sp.Expr], v: Tuple[sp.Expr, sp.Expr]):
    return (u[0] * v[0] - u[1] * v[1],
            u[0] * v[1] + u[1] * v[0])


def rotation(a: sp.Expr, b: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[a, -b], [b, a]])


def trunc(poly: sp.Expr, variable: sp.Symbol, degree: int) -> sp.Expr:
    return sp.series(poly, variable, 0, degree + 1).removeO().expand()


def main() -> None:
    t, h, s, p, q, r, w = sp.symbols("t h s p q r w", real=True)
    a, b, c, d, x, y = sp.symbols("a b c d x y", real=True)
    A, B = (1 - t*t)/(1 + t*t), 2*t/(1 + t*t)
    check("Cayley norm", A*A + B*B - 1)
    check("Cayley complex formula", cayley(t) - A - sp.I*B)
    check("Cayley inverse chart", B/(1 + A) - t)
    check("Cayley inverse unit", cayley(t)*cayley(-t) - 1)
    check("Cayley affine product", cayley(t)*cayley(s)
          - cayley((t+s)/(1-t*s)))
    check("Homogeneous norm factorization",
          (s*p-t*q)**2 + (s*q+t*p)**2 - (s*s+t*t)*(p*p+q*q))
    check("Homogeneous group law", homogeneous(s,t)*homogeneous(p,q)
          - homogeneous(s*p-t*q,s*q+t*p))
    left = product(product((s,t),(p,q)),(r,w))
    right = product((s,t),product((p,q),(r,w)))
    check("Homogeneous associativity, real coordinate", left[0]-right[0])
    check("Homogeneous associativity, imaginary coordinate", left[1]-right[1])
    check("Chart value at zero", cayley(sp.Integer(0)) - 1)
    check("Chart value at one", cayley(sp.Integer(1)) - sp.I)
    check("Exceptional product ts=1", cayley(t)*cayley(1/t) + 1)
    check("Exceptional product with infinity", -cayley(t) - cayley(-1/t))
    check("Near-half-turn formula", cayley(t)+1 - 2*(1+sp.I*t)/(1+t*t))
    check("Invariant differential", A*sp.diff(B,t)-B*sp.diff(A,t)-2/(1+t*t))

    R = rotation(a,b)
    check_matrix("Rotation matrix product", R*rotation(c,d)
                 -rotation(a*c-b*d,a*d+b*c))
    check_matrix("Orthogonal norm factor", R.T*R - (a*a+b*b)*sp.eye(2))
    check("Matrix determinant", R.det()-a*a-b*b)
    check("Displacement norm square",
          ((a-c)*x-(b-d)*y)**2 + ((b-d)*x+(a-c)*y)**2
          - ((a-c)**2+(b-d)**2)*(x*x+y*y))
    check("Cayley example longitudinal correction",
          A/t - (1/t - 2*t/(1+t*t)))
    check("Cayley example transverse correction", B/t - 2/(1+t*t))
    check("Cayley chord square", (A-1)**2+B**2 - 4*t*t/(1+t*t))

    e1 = sp.Matrix([[sp.I,0],[0,-sp.I]])
    e2 = sp.Matrix([[0,1],[-1,0]])
    E = e1*e2
    check_matrix("Clifford bivector square", E*E+sp.eye(2))
    spin = a*sp.eye(2)+b*E
    spin_conjugate = a*sp.eye(2)-b*E
    check_matrix("Clifford double angle", spin*e1*spin_conjugate
                 - ((a*a-b*b)*e1+2*a*b*e2))

    C8 = trunc(cayley(t), t, 8)
    expected_C8 = 1 + sum(2*sp.I**n*t**n for n in range(1,9))
    check("Cayley Taylor coefficients through degree 8", C8-expected_C8)
    angle = trunc(2*sp.atan(t), t, 8)
    exp_angle = sum((sp.I*angle)**n/sp.factorial(n) for n in range(9))
    check("Exp of twice arctangent through degree 8",
          trunc(exp_angle,t,8)-C8)
    E10 = sum((sp.I*h)**n/sp.factorial(n) for n in range(11))
    check("Formal unit identity through degree 10",
          trunc(E10*E10.subs(h,-h),h,10)-1)
    expected_chord_ratio = 1-h**2/24+h**4/1920-h**6/322560+h**8/92897280
    check("Chord-angle ratio through degree 8",
          trunc(2*sp.sin(h/2)/h,h,8)-expected_chord_ratio)
    expected_angle = sum(2*(-1)**n*t**(2*n+1)/sp.Integer(2*n+1)
                         for n in range(6))
    check("Logarithmic Cayley angle through degree 11",
          trunc(-sp.I*(sp.log(1+sp.I*t)-sp.log(1-sp.I*t)),t,11)
          -expected_angle)

    report = {
        "scope": "Exact finite symbolic checks, not formal verification of surreal theorems",
        "sympy_version": sp.__version__,
        "checks_passed": len(RESULTS),
        "checks": RESULTS,
    }
    path = Path(__file__).resolve().with_name("verification_results.json")
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"All {len(RESULTS)} finite symbolic checks passed.")
    print(f"Report: {path.name}")


if __name__ == "__main__":
    main()
