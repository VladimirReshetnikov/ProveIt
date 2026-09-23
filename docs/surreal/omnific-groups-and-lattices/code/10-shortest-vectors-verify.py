#!/usr/bin/env python3
"""Exact finite algebra checks for the omnific-lattice research article.

Requires Python 3.9+ and SymPy. This program does NOT implement surreal
numbers, verify infima or coinitiality, or formalize the mathematical proofs.
Run: python verify.py
"""
from __future__ import annotations

from math import gcd
from typing import List, Tuple

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install with: python -m pip install sympy") from exc


def zero(expr: sp.Expr, name: str) -> None:
    """Raise a useful error when an exact symbolic identity does not simplify."""
    remainder = sp.simplify(expr)
    if remainder != 0:
        raise AssertionError(f"{name}: nonzero remainder {remainder}")


def zero_matrix(matrix: sp.Matrix, name: str) -> None:
    for row in range(matrix.rows):
        for col in range(matrix.cols):
            zero(matrix[row, col], f"{name}[{row},{col}]")


def main() -> None:
    eps = sp.Symbol("epsilon", positive=True)
    alpha = sp.Symbol("alpha", real=True)
    root2 = sp.sqrt(2)
    q = sp.Matrix([[1 + eps, -alpha], [-alpha, alpha**2 + eps]])
    t = sp.Matrix([
        [sp.sqrt(1 + eps), -alpha / sp.sqrt(1 + eps)],
        [0, sp.sqrt(eps * (1 + alpha**2 + eps) / (1 + eps))],
    ])
    zero(q.det() - eps * (1 + alpha**2 + eps), "general determinant")
    zero_matrix(t.T * t - q, "triangular Gram identity")
    zero(t.det()**2 - eps * (1 + alpha**2 + eps), "squared triangular determinant")
    zero(q.subs(alpha, root2).det() - eps * (3 + eps), "binary determinant")
    print("PASS: general determinant, triangular Gram identity, and binary specialization")

    p, r = sp.symbols("p q", integer=True)
    pn, qn = p + 2*r, p + r
    zero(pn**2 - 2*qn**2 + (p**2 - 2*r**2), "Pell norm recurrence")
    zero(p*qn - r*pn - (p**2 - 2*r**2), "consecutive Pell determinant identity")
    zero(pn - root2*qn - (1-root2)*(p-root2*r), "Pell residual recurrence")
    zero(pn + root2*qn - (1+root2)*(p+root2*r), "Pell positive root recurrence")
    print("PASS: four exact symbolic Pell recurrence identities")

    values: List[Tuple[int, int]] = [(1, 0)]
    for _ in range(81):
        pp, qq = values[-1]
        values.append((pp + 2*qq, pp + qq))
    for n in range(81):
        pp, qq = values[n]
        pp1, qq1 = values[n + 1]
        assert pp*pp - 2*qq*qq == (-1)**n, f"Pell norm n={n}"
        assert pp*qq1 - qq*pp1 == (-1)**n, f"Pell basis determinant n={n}"
        assert gcd(pp, qq) == 1, f"Pell coordinate gcd n={n}"
    print("PASS: Pell indices 0..80 (81 norms, 81 consecutive determinants, 81 gcd checks)")

    d1, d2 = sp.symbols("D1 D2", positive=True)
    mu, s, u = sp.symbols("mu s t", real=True)
    gram = sp.Matrix([[d1, mu*d1], [mu*d1, d2 + mu**2*d1]])
    v = sp.Matrix([s, u])
    zero((v.T*gram*v)[0] - (d1*(s + mu*u)**2 + d2*u**2), "Gram-Schmidt energy")
    print("PASS: two-dimensional real Gram-Schmidt energy identity")

    e1 = sp.Matrix([1, 0, 0])
    w = sp.Matrix([0, 1, root2])
    q0 = sp.Matrix([[0, 0, 0], [0, 2, -root2], [0, -root2, 1]])
    q1 = sp.diag(1, 0, 0)
    q2 = sp.diag(0, 1, 1)
    zero_matrix(q0*e1, "first kernel e1")
    zero_matrix(q0*w, "first kernel irrational vector")
    zero_matrix(q1*w, "second kernel irrational vector")
    q3 = q0 + eps*q1 + eps**2*q2
    zero(q3.det() - eps**3*(3 + eps**2), "three-scale determinant")
    zero((e1.T*q3*e1)[0] - eps, "primitive-only energy")
    zero((w.T*q3*w)[0] / 3 - eps**2, "normalized deepest direction")
    qs = q0 + eps*sp.eye(3)
    zero(qs.det() - eps**2*(3 + eps), "shortest-but-no-cover determinant")
    print("PASS: three-dimensional kernels, determinants, and distinguished energies")

    eta = sp.Symbol("eta", positive=True)
    center = sp.Matrix([sp.Rational(1, 2) + eta, sp.Rational(1, 4)])
    def target_energy(x: int, y: int) -> sp.Expr:
        dx = x - center[0]
        dy = y - center[1]
        return sp.expand(dx**2 + eps*(dy - dx/2)**2)
    delta10 = target_energy(1, 0) - target_energy(0, 0)
    delta11 = target_energy(1, 1) - target_energy(1, 0)
    zero(delta10 - (-2*eta + eps*(sp.Rational(1, 4) - eta/2)), "target branch switch")
    zero(delta11 - eps*eta, "target fine tie break")
    print("PASS: both exact infinitesimal-target branch comparison identities")
    print("\nAll finite checks passed.")
    print(f"SymPy version: {sp.__version__}")
    print("Scope: exact finite identities only; no surreal arithmetic engine or formal proof verification.")


if __name__ == "__main__":
    main()
