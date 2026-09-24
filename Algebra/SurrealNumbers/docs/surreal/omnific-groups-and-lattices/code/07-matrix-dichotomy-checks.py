#!/usr/bin/env python3
"""Exact finite checks accompanying the omnific matrix-size article.

Requires Python 3.9+ and SymPy. Run: python checks.py
These are symbolic identities and finite regression examples, not verification
of the class-size, support, normal-form, or arbitrary-word theorems.
"""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path
from typing import Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def elementary(n: int, i: int, j: int, x: Any) -> sp.Matrix:
    """Elementary matrix, using zero-based indices."""
    if n < 2 or not (0 <= i < n and 0 <= j < n) or i == j:
        raise ValueError("Require n >= 2 and distinct valid indices.")
    result = sp.eye(n)
    result[i, j] = x
    return result


def commutator(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return (a * b * a.inv() * b.inv()).applyfunc(sp.cancel)


def same_matrix(a: sp.Matrix, b: sp.Matrix) -> bool:
    return a.shape == b.shape and all(sp.simplify(x) == 0 for x in a - b)


def main() -> int:
    results: list[dict[str, Any]] = []

    def check(name: str, value: bool, detail: str) -> None:
        value = bool(value)
        results.append({"name": name, "passed": value, "detail": detail})
        if not value:
            raise AssertionError(name)

    u, v, alpha, z, t, x = sp.symbols("u v alpha z t x")

    # The three-index multiplication law is independent of surreal arithmetic.
    for i, j, k in itertools.permutations(range(3)):
        lhs = commutator(elementary(3, i, j, u), elementary(3, j, k, v))
        rhs = elementary(3, i, k, u * v)
        check(f"Steinberg commutator ({i+1},{j+1},{k+1})", same_matrix(lhs, rhs),
              "Polynomial identity for formal commuting parameters u,v.")

    upper, lower = elementary(2, 0, 1, t), elementary(2, 1, 0, t)
    expected = sp.Matrix([[1 + t**2 + t**4, -t**3], [t**3, 1 - t**2]])
    check("Two-row nonabelian detector", same_matrix(commutator(upper, lower), expected),
          "Exact displayed matrix; nonidentity since its off-diagonal entries are nonzero.")

    d_i = sp.diag(sp.I, -sp.I)
    check("Gaussian diagonal commutator",
          same_matrix(commutator(d_i, elementary(2, 0, 1, -x / 2)),
                      elementary(2, 0, 1, x)),
          "[diag(i,-i),U(-x/2)] = U(x).")

    q = sp.Matrix([[alpha, 1], [-alpha**2, -alpha]])
    matrix = sp.eye(2) + z**2 * q
    check("Square-zero coefficient matrix", same_matrix(q * q, sp.zeros(2)),
          "Q_alpha^2 = 0 for a formal parameter alpha.")
    check("Unipotent determinant", sp.expand(matrix.det()) == 1,
          "det(I + z^2 Q_alpha) = 1.")
    check("Constant reduction in the monomial parameter",
          same_matrix(matrix.subs(z, 0), sp.eye(2)),
          "All nonconstant terms vanish at z=0 in this finite symbolic model.")

    # Exact explicit stabilized word; z stands for omega^a in the article.
    a = elementary(3, 0, 2, z) * elementary(3, 1, 2, -alpha * z)
    b = elementary(3, 2, 0, alpha * z) * elementary(3, 2, 1, z)
    check("One-step stabilized commutator",
          same_matrix(commutator(a, b), sp.diag(matrix, sp.Matrix([[1]]))),
          "[e13(z)e23(-alpha*z),e31(alpha*z)e32(z)] = diag(M_alpha(z^2),1).")

    row = sp.Matrix([[alpha * z, z]])
    col = sp.Matrix([z, -alpha * z])
    check("Vanishing inner scalar", same_matrix(row * col, sp.zeros(1)),
          "wv=0, the hypothesis of the block commutator identity.")
    ratio = (1 + alpha * z**2) / (-alpha**2 * z**2)
    check("Cusp ratio formula",
          sp.cancel(ratio + 1 / alpha + 1 / (alpha**2 * z**2)) == 0,
          "Rational-function identity for alpha,z nonzero; no standard-part computation is asserted.")

    for power in range(1, 9):
        check(f"Unipotent power {power}",
              same_matrix(matrix**power, sp.eye(2) + power * z**2 * q),
              "Finite regression instance of (I+TQ)^m=I+mTQ when Q^2=0.")

    # Reduced alternating target words. Each G_c has lower-left entry 1;
    # each U(q*t) is nonconstant for q != 0. These are finite tests only.
    target_words = 0
    s = sp.Matrix([[0, -1], [1, 0]])
    for length in range(1, 5):
        for coefficients in itertools.product((-2, 1, 3), repeat=length):
            word = sp.eye(2)
            for j, coefficient in enumerate(coefficients):
                g = s * elementary(2, 0, 1, j - 1)
                word = word * g * elementary(2, 0, 1, coefficient * t)
            word = word.applyfunc(sp.expand)
            if word == sp.eye(2) or word == -sp.eye(2):
                raise AssertionError("Reduced alternating polynomial word became scalar")
            if sp.expand(word.det()) != 1:
                raise AssertionError("Polynomial target word lost determinant one")
            target_words += 1
    check("Reduced alternating target-word regressions", True,
          f"{target_words} exact words of lengths 1--4 checked; this is not an arbitrary-word proof.")

    report = {
        "status": "PASS",
        "python": sys.version.split()[0],
        "sympy": sp.__version__,
        "check_count": len(results),
        "polynomial_word_examples": target_words,
        "checks": results,
        "limits": [
            "No Lean proof is produced or checked.",
            "No proper-class or transfinite-support statement is verified computationally.",
            "Finite word tests are examples, not a proof of the amalgam theorem.",
            "All computations are exact symbolic computations, not floating-point experiments."
        ],
    }
    output = Path(__file__).resolve().with_name("checks-results.json")
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(results)} checks, including {target_words} exact target-word examples.")
    print(f"Python {report['python']}; SymPy {report['sympy']}.")
    print(f"Report written to {output.name}.")
    print("Scope: finite symbolic identities only; no Lean or transfinite verification.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
