#!/usr/bin/env python3
"""Exact finite checks for the accompanying surcomplex research manuscript.

Requires Python 3.10+ and SymPy. This is not a formal verification of the
support lemmas, transfinite recursions, or theorems. A failed assertion exits
with a nonzero status; a report is written only after all checks pass.
"""
from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

t, x, y, w, zeta, a, b, T, c, z = sp.symbols("t x y w zeta a b T c z")
checks: list[str] = []


def zero(expression: sp.Expr | sp.MatrixBase, label: str) -> None:
    """Assert exact symbolic zero, including each entry of a matrix."""
    entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
    failures = [sp.simplify(e) for e in entries if sp.simplify(e) != 0]
    if failures:
        raise AssertionError(f"{label}: nonzero expression(s): {failures}")
    checks.append(label)


def cyclotomic_reduce(expression: sp.Expr) -> sp.Expr:
    """Reduce polynomial zeta expressions modulo zeta**3 - 1."""
    return sp.rem(sp.expand(expression), zeta**3 - 1, zeta)


def sum_over_cube_roots(expression: sp.Expr) -> sp.Expr:
    """The exact sum over all three roots of unity, for polynomial input."""
    remainder = sp.Poly(cyclotomic_reduce(expression), zeta)
    return 3 * remainder.coeff_monomial(1)


def matrix_polynomial(expression: sp.Expr, matrices: dict[sp.Symbol, sp.MatrixBase]) -> sp.Matrix:
    """Evaluate a polynomial in commuting matrices, with symbolic scalars."""
    variables = tuple(matrices)
    size = next(iter(matrices.values())).rows
    result = sp.zeros(size)
    for powers, coefficient in sp.Poly(expression, *variables).terms():
        term = sp.eye(size) * coefficient
        for variable, exponent in zip(variables, powers):
            term = term * matrices[variable] ** exponent
        result += term
    return result


# 1. Coupled system x**2=t*y, y**2=t*x.
Wx = sp.Matrix([[0, 0, 0, 0], [1, 0, 0, t**2], [0, t, 0, 0], [0, 0, 1, 0]])
Wy = sp.Matrix([[0, 0, 0, 0], [0, 0, t, 0], [1, 0, 0, t**2], [0, 1, 0, 0]])
zero(Wx * Wy - Wy * Wx, "Coupled multiplication matrices commute")
zero(Wx**2 - t * Wy, "Matrix relation x^2 = t y")
zero(Wy**2 - t * Wx, "Matrix relation y^2 = t x")
zero(Wx.charpoly(T).as_expr() - (T**4 - t**3 * T), "Characteristic polynomial of x")
zero(Wy.charpoly(T).as_expr() - (T**4 - t**3 * T), "Characteristic polynomial of y")

unit = sp.Matrix([1, 0, 0, 0])
lam = sp.Matrix([[0, 0, 0, 1]])
basis = [sp.Integer(1), x, y, x * y]
mult = [sp.eye(4), Wx, Wy, Wx * Wy]
G = sp.Matrix(4, 4, lambda i, j: (lam * mult[i] * mult[j] * unit)[0])
expected_G = sp.Matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, t**2]])
zero(G - expected_G, "Coupled residue Gram matrix")
zero(G.det() - 1, "Coupled residue Gram determinant equals 1")
dual = G.inv()
expected_dual = sp.Matrix.hstack(sp.Matrix([-t**2, 0, 0, 1]), sp.Matrix([0, 0, 1, 0]),
                                sp.Matrix([0, 1, 0, 0]), sp.Matrix([1, 0, 0, 0]))
zero(dual - expected_dual, "Coupled residue-dual basis")
euler_coordinates = sum((mult[j] * dual[:, j] for j in range(4)), sp.zeros(4, 1))
zero(euler_coordinates - sp.Matrix([-t**2, 0, 0, 4]), "Coupled trace element equals 4xy-t^2")
Euler = 4 * Wx * Wy - t**2 * sp.eye(4)
for k, H in enumerate(basis + [x**5 + y**4 + t*x*y, (x+y)**6]):
    MH = matrix_polynomial(H, {x: Wx, y: Wy})
    zero(sp.trace(MH) - (lam * MH * Euler * unit)[0], f"Coupled trace identity, test {k+1}")
    weights = -H.subs({x: 0, y: 0}) / t**2
    weights += sum_over_cube_roots(H.subs({x: t*zeta, y: t*zeta**2})) / (3*t**2)
    zero(weights - (lam * MH * unit)[0], f"Coupled root-weight formula, test {k+1}")
zero(cyclotomic_reduce((x**2-t*y).subs({x: t*zeta, y: t*zeta**2})), "Nonzero roots solve first coupled equation")
zero(cyclotomic_reduce((y**2-t*x).subs({x: t*zeta, y: t*zeta**2})), "Nonzero roots solve second coupled equation")
zero(cyclotomic_reduce((4*x*y-t**2).subs({x: t*zeta, y: t*zeta**2})) - 3*t**2,
     "Jacobian at the three nonzero roots")

# 2. Nonpolynomial sine example. Check all residual coefficients of t^j, j<6.
X = t*zeta + (2+zeta**2)*t**3/9
Y = t*zeta**2 + (2+zeta)*t**3/9
for k, residual in enumerate([sp.sin(X)**2-t*Y, sp.sin(Y)**2-t*X]):
    truncated = sp.series(residual, t, 0, 6).removeO()
    zero(cyclotomic_reduce(truncated), f"Sine root expansion equation {k+1}, residual O(t^6)")
sine_J = 4*sp.sin(X)*sp.cos(X)*sp.sin(Y)*sp.cos(Y)-t**2
zero(cyclotomic_reduce(sp.series(sine_J, t, 0, 4).removeO()) - 3*t**2,
     "Sine Jacobian leading term 3t^2, remainder O(t^4)")

# 3. Cubic residue versus trace pairings.
W = sp.Matrix([[0, 0, b], [1, 0, a], [0, 1, 0]])
u3 = sp.Matrix([1, 0, 0])
l3 = sp.Matrix([[0, 0, 1]])
Gc = sp.Matrix(3, 3, lambda i, j: (l3 * W**(i+j) * u3)[0])
Tc = sp.Matrix(3, 3, lambda i, j: sp.trace(W**(i+j)))
zero(Gc - sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, a]]), "Cubic residue Gram matrix")
zero(Gc.det() + 1, "Cubic residue Gram determinant equals -1")
zero(Tc - sp.Matrix([[3, 0, 2*a], [0, 2*a, 3*b], [2*a, 3*b, 2*a**2]]), "Cubic trace Gram matrix")
zero(Tc.det() - (4*a**3-27*b**2), "Cubic trace Gram determinant equals discriminant")
zero(sp.discriminant(w**3-a*w-b, w) - (4*a**3-27*b**2), "Cubic polynomial discriminant")
euler_c = sum((W**j * Gc.inv()[:, j] for j in range(3)), sp.zeros(3, 1))
zero(euler_c - sp.Matrix([-a, 0, 3]), "Cubic trace element equals P_w")
Pc = w**3-3*t**2*w-2*t**3
zero(Pc - (w-2*t)*(w+t)**2, "Repeated-root cubic factorization")
partial_fractions = 1/(9*t**2*(w-2*t)) - 1/(9*t**2*(w+t)) - 1/(3*t*(w+t)**2)
zero(1/Pc - partial_fractions, "Repeated-root partial fraction identity")
for degree in range(8):
    H = w**degree
    residue = sp.Poly(sp.rem(H, Pc, w), w).coeff_monomial(w**2)
    formula = (H.subs(w, 2*t)-H.subs(w, -t))/(9*t**2)-sp.diff(H,w).subs(w,-t)/(3*t)
    zero(residue-formula, f"Double-root residue formula on w^{degree}")
    specialized_trace = sp.trace((W.subs({a: 3*t**2, b: 2*t**3}))**degree)
    zero(specialized_trace-H.subs(w,2*t)-2*H.subs(w,-t), f"Double-root trace formula on w^{degree}")

# 4. A finite jet of the matrix-division formula, m=2, through t^4.
# H consists of degree-20 Taylor polynomials of exp(w), sin(w).
Aerr = sp.Matrix([[w, 1], [w**3, 0]])
Hjet = sp.Matrix([sp.series(sp.exp(w),w,0,21).removeO(), sp.series(sp.sin(w),w,0,21).removeO()])

def R2(V: sp.MatrixBase) -> sp.Matrix:
    return V.applyfunc(lambda f: sp.expand(f).subs(w,0) + sp.diff(sp.expand(f),w).subs(w,0)*w)

def D2(V: sp.MatrixBase) -> sp.Matrix:
    return ((V-R2(V))/w**2).applyfunc(sp.cancel)

term = D2(Hjet)
Q = sp.zeros(2, 1)
for k in range(5):
    Q += (-t)**k * term
    term = D2(Aerr * term)
Rfull = R2(Hjet - t*Aerr*Q)
R = Rfull.applyfunc(lambda f: sp.series(f,t,0,5).removeO())
residual = Hjet - (w**2*sp.eye(2)+t*Aerr)*Q - R
zero(residual.applyfunc(lambda f: sp.series(sp.expand(f),t,0,5).removeO()),
     "Matrix division identity through t^4 for degree-20 analytic Taylor jets")
for j in range(2):
    if sp.degree(R[j], w) >= 2:
        raise AssertionError("Matrix remainder has degree >= 2")
checks.append("Matrix remainder entries have degree less than 2 in w")

# 5. Monodromy illustration's displayed coefficient and discriminant.
root_approx = c + t/(3*c)
zero(sp.series(root_approx**3-c**3-t*root_approx,t,0,3).removeO(),
     "Lifted cubic root c+t/(3c) solves the equation through t^2")
zero(sp.discriminant(w**3-z-t*w,w)-(4*t**3-27*z**2), "Monodromy illustration discriminant")

report = [
    "EXACT SYMBOLIC VERIFICATION REPORT",
    "Article: Hartogs Coherence, Finite Maps, and Residue Duality over the Surcomplex Numbers",
    f"Run time (UTC): {datetime.now(timezone.utc).isoformat(timespec='seconds')}",
    f"Python: {sys.version.split()[0]}",
    f"SymPy: {sp.__version__}",
    f"Result: ALL {len(checks)} CHECKS PASSED",
    "",
    "Scope: finite exact identities and explicitly truncated example series only.",
    "Not verified by this script: the general theorems, arbitrary Hahn supports,",
    "transfinite recursion, class-set foundations, or publication novelty.",
    "Sine expansion: equation residuals vanish through degree 5 in t;",
    "the leading Jacobian is checked modulo O(t^4), with zeta^3=1.",
    "Matrix division: degree-20 Taylor numerators of exp(w) and sin(w),",
    "with the division identity checked coefficientwise through degree 4 in t.",
    "",
]
report += [f"{i:02d}. PASS: {label}" for i, label in enumerate(checks, 1)]
output = Path(__file__).with_name("verification_report.txt")
output.write_text("\n".join(report)+"\n", encoding="utf-8")
print(f"All {len(checks)} exact checks passed. Report: {output}")
