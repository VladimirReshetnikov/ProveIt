#!/usr/bin/env python3
"""Exact finite checks accompanying the surquaternion article.

Requires Python 3.9+ and SymPy. This is NOT a theorem prover for surreal
numbers or Hahn summability. It checks the listed polynomial/rational
identities and finite formal expansions using central symbolic variables.

Usage:
    python code/verify.py
    python code/verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

Quat = Tuple[s.Expr, s.Expr, s.Expr, s.Expr]
ZERO: Quat = (s.S.Zero, s.S.Zero, s.S.Zero, s.S.Zero)
ONE: Quat = (s.S.One, s.S.Zero, s.S.Zero, s.S.Zero)
I: Quat = (s.S.Zero, s.S.One, s.S.Zero, s.S.Zero)
J: Quat = (s.S.Zero, s.S.Zero, s.S.One, s.S.Zero)
K: Quat = (s.S.Zero, s.S.Zero, s.S.Zero, s.S.One)


def add(*values: Quat) -> Quat:
    return tuple(sum((q[j] for q in values), s.S.Zero) for j in range(4))  # type: ignore


def scale(c: s.Expr, q: Quat) -> Quat:
    return tuple(c * x for x in q)  # type: ignore


def neg(q: Quat) -> Quat:
    return scale(-1, q)


def sub(p: Quat, q: Quat) -> Quat:
    return add(p, neg(q))


def mul(p: Quat, q: Quat) -> Quat:
    a, b, c, d = p
    e, f, g, h = q
    return (
        a*e - b*f - c*g - d*h,
        a*f + b*e + c*h - d*g,
        a*g - b*h + c*e + d*f,
        a*h + b*g - c*f + d*e,
    )


def conj(q: Quat) -> Quat:
    return (q[0], -q[1], -q[2], -q[3])


def norm(q: Quat) -> s.Expr:
    return sum((x*x for x in q), s.S.Zero)


def inv(q: Quat) -> Quat:
    n = s.expand(norm(q))
    if n == 0:
        raise ZeroDivisionError("Cannot invert the zero quaternion.")
    return scale(1/n, conj(q))


def power(q: Quat, n: int) -> Quat:
    if n < 0:
        return power(inv(q), -n)
    result = ONE
    for _ in range(n):
        result = mul(result, q)
    return result


def comm(p: Quat, q: Quat) -> Quat:
    return sub(mul(p, q), mul(q, p))


def rho(q: Quat) -> s.Matrix:
    a, b, c, d = q
    return s.Matrix([[a+s.I*b, c+s.I*d], [-c+s.I*d, a-s.I*b]])


def evaluate(coefficients: Sequence[Quat], q: Quat) -> Quat:
    """Evaluate coefficients ordered from degree zero, on the RIGHT."""
    result = ZERO
    for a in reversed(coefficients):
        result = add(mul(q, result), a)
    return result


class Checks:
    def __init__(self) -> None:
        self.records: List[dict] = []

    def zero(self, name: str, expressions: Iterable[s.Expr]) -> None:
        expressions = list(expressions)
        failures = []
        for index, expression in enumerate(expressions):
            reduced = s.cancel(s.expand(expression))
            if reduced != 0:
                reduced = s.simplify(reduced)
            if reduced != 0:
                failures.append({"component": index, "residual": str(reduced)})
        self.records.append({
            "name": name,
            "scalar_identities": len(expressions),
            "passed": not failures,
            **({"failures": failures} if failures else {}),
        })
        print(("PASS " if not failures else "FAIL ") + name)

    def quat(self, name: str, actual: Quat, expected: Quat) -> None:
        self.zero(name, sub(actual, expected))

    def scalar(self, name: str, actual: s.Expr, expected: s.Expr = s.S.Zero) -> None:
        self.zero(name, [actual-expected])

    def matrix(self, name: str, actual: s.Matrix, expected: s.Matrix) -> None:
        self.zero(name, list(actual-expected))


def run_checks() -> Checks:
    c = Checks()
    basis = [ONE, I, J, K]
    table = [
        [ONE, I, J, K],
        [I, neg(ONE), K, neg(J)],
        [J, neg(K), neg(ONE), I],
        [K, J, neg(I), neg(ONE)],
    ]
    names = ["1", "i", "j", "k"]
    for row in range(4):
        for col in range(4):
            c.quat(f"Hamilton table: {names[row]} * {names[col]}",
                   mul(basis[row], basis[col]), table[row][col])

    p: Quat = tuple(s.symbols("a b c d", real=True))  # type: ignore
    q: Quat = tuple(s.symbols("e f g h", real=True))  # type: ignore
    r: Quat = tuple(s.symbols("u v w z", real=True))  # type: ignore
    c.quat("generic associativity", mul(mul(p, q), r), mul(p, mul(q, r)))
    c.quat("conjugation reverses multiplication", conj(mul(p, q)), mul(conj(q), conj(p)))
    c.quat("q conjugate(q) is scalar norm", mul(p, conj(p)), scale(norm(p), ONE))
    c.scalar("generic norm multiplicativity", norm(mul(p, q)), norm(p)*norm(q))
    c.quat("quadratic identity", add(power(p, 2), scale(-2*p[0], p), scale(norm(p), ONE)), ZERO)
    c.quat("generic inverse on the right", mul(p, inv(p)), ONE)
    c.quat("generic inverse on the left", mul(inv(p), p), ONE)
    c.matrix("complex representation multiplication", rho(mul(p, q)), rho(p)*rho(q))
    c.matrix("complex representation adjoint", rho(conj(p)), rho(p).conjugate().T)
    c.scalar("complex representation determinant", rho(p).det(), norm(p))
    c.scalar("complex representation trace", s.trace(rho(p)), 2*p[0])

    x1, x2, x3 = s.symbols("x1 x2 x3", real=True)
    x: Quat = (s.S.Zero, x1, x2, x3)
    a, b, cc, d = p
    cross = (cc*x3-d*x2, d*x1-b*x3, b*x2-cc*x1)
    dot = b*x1+cc*x2+d*x3
    vector = (b, cc, d)
    rod: Quat = (s.S.Zero,) + tuple(
        (a*a-b*b-cc*cc-d*d)*x[j+1] + 2*dot*vector[j] + 2*a*cross[j]
        for j in range(3)
    )  # type: ignore
    c.quat("Rodrigues polynomial formula without unit assumption", mul(mul(p, x), conj(p)), rod)
    pure: Quat = (s.S.Zero, b, cc, d)
    c.quat("imaginary commutator is twice cross product", comm(pure, x),
           (s.S.Zero,) + tuple(2*y for y in cross))  # type: ignore
    reconstructed = scale(-s.Rational(1, 4), add(
        mul(comm(pure, I), I), mul(comm(pure, J), J), mul(comm(pure, K), K)))
    c.quat("inner derivation reconstruction", reconstructed, pure)

    X = s.Symbol("X", real=True)
    polynomial = [K, neg(add(I, J)), ONE]
    c.quat("factor example: P(i)=0", evaluate(polynomial, I), ZERO)
    c.quat("factor example: P(j)=2k", evaluate(polynomial, J), scale(2, K))
    p_at_X = evaluate(polynomial, scale(X, ONE))
    c.scalar("factor example: normal polynomial", norm(p_at_X), (X*X+1)**2)
    A, B = neg(add(I, J)), sub(K, ONE)
    c.quat("sphere remainder yields root i", neg(mul(B, inv(A))), I)
    c.quat("square root 2+i of 3+4i", power(add(scale(2, ONE), I), 2), add(scale(3, ONE), scale(4, I)))
    c.quat("negative scalar has a non-axis square root",
           power(scale(3, add(scale(s.Rational(3, 5), I), scale(s.Rational(4, 5), J))), 2),
           scale(-9, ONE))

    t = s.Symbol("t", positive=True)
    infinitesimal = add(scale(t, I), scale(t*t, J))
    cayley = mul(add(ONE, infinitesimal), inv(sub(ONE, infinitesimal)))
    c.scalar("rational Cayley chart has unit norm", norm(cayley), 1)
    c.quat("rational Cayley chart inverse", mul(sub(cayley, ONE), inv(add(cayley, ONE))), infinitesimal)
    c.quat("two-scale inverse", inv(add(ONE, infinitesimal)),
           scale(1/(1+t*t+t**4), sub(ONE, infinitesimal)))
    for m in range(6):
        partial = add(*(power(neg(infinitesimal), n) for n in range(m+1)))
        error = sub(inv(add(ONE, infinitesimal)), partial)
        exact = mul(power(neg(infinitesimal), m+1), inv(add(ONE, infinitesimal)))
        c.quat(f"exact geometric remainder through degree {m}", error, exact)

    def trunc_expr(expr: s.Expr, order: int) -> s.Expr:
        poly = s.Poly(s.expand(expr), t)
        return s.Add(*(coef*t**monomial[0] for monomial, coef in poly.terms()
                       if monomial[0] < order))

    def trunc(value: Quat, order: int) -> Quat:
        return tuple(trunc_expr(component, order) for component in value)  # type: ignore

    def tmul(left: Quat, right: Quat, order: int) -> Quat:
        return trunc(mul(left, right), order)

    def exp_trunc(value: Quat, order: int) -> Quat:
        result, term = ONE, ONE
        for n in range(1, order):
            term = tmul(term, value, order)
            result = add(result, scale(1/s.factorial(n), term))
        return trunc(result, order)

    def log_trunc(unit: Quat, order: int) -> Quat:
        value = sub(unit, ONE)
        result, term = ZERO, ONE
        for n in range(1, order):
            term = tmul(term, value, order)
            result = add(result, scale(s.Rational((-1)**(n+1), n), term))
        return trunc(result, order)

    tx, ty = scale(t, I), scale(t, J)
    bch = log_trunc(tmul(exp_trunc(tx, 4), exp_trunc(ty, 4), 4), 4)
    bch_expected = add(scale(t-t**3/3, add(I, J)), scale(t*t, K))
    c.quat("BCH through degree three", bch, bch_expected)
    mixed_y = scale(t*t, J)
    groupcomm = ONE
    for value in [tx, mixed_y, neg(tx), neg(mixed_y)]:
        groupcomm = tmul(groupcomm, exp_trunc(value, 4), 4)
    c.quat("group commutator leading term", groupcomm, add(ONE, scale(2*t**3, K)))
    general_small = add(tx, mixed_y, scale(-2*t**3, K))
    c.quat("log(exp(X)) modulo t^7", log_trunc(exp_trunc(general_small, 7), 7), general_small)
    c.scalar("pure exponential has norm one modulo t^7",
             trunc_expr(norm(exp_trunc(general_small, 7)), 7), 1)
    c.quat("exp(X)exp(-X) modulo t^7",
           tmul(exp_trunc(general_small, 7), exp_trunc(neg(general_small), 7), 7), ONE)

    g, e, lam = s.symbols("gap perturbation lambda", real=True)
    complex_A = s.Matrix([[0, s.I*e, 0, 0], [-s.I*e, g, 0, 0],
                          [0, 0, 0, -s.I*e], [0, 0, s.I*e, g]])
    c.matrix("two-scale complex matrix is Hermitian", complex_A, complex_A.conjugate().T)
    c.scalar("two-scale complex characteristic polynomial",
             (lam*s.eye(4)-complex_A).det(), (lam**2-g*lam-e**2)**2)
    root = s.sqrt(1+4*t*t)
    minus, plus = t*(1-root)/2, t*(1+root)/2
    c.scalar("lower eigenvalue solves quadratic", minus**2-t*minus-t**4)
    c.scalar("upper eigenvalue solves quadratic", plus**2-t*plus-t**4)
    c.scalar("lower eigenvalue expansion through t^9",
             s.series(minus, t, 0, 10).removeO(), -t**3+t**5-2*t**7+5*t**9)
    c.scalar("upper eigenvalue expansion through t^9",
             s.series(plus, t, 0, 10).removeO(), t+t**3-t**5+2*t**7-5*t**9)
    c.scalar("projector off-diagonal expansion through t^7",
             s.series(-t/root, t, 0, 8).removeO(), -t+2*t**3-6*t**5+20*t**7)
    Acomplex2 = s.Matrix([[0, s.I*t*t], [-s.I*t*t, t]])
    P = (plus*s.eye(2)-Acomplex2)/(plus-minus)
    c.matrix("lower spectral projector is idempotent", P*P, P)
    c.matrix("lower spectral projector is Hermitian", P, P.conjugate().T)
    c.matrix("lower spectral projector eigen-equation", Acomplex2*P, minus*P)

    real_a, real_x, real_y, real_z = s.symbols("a0 x0 y0 z0", real=True)
    variables = [real_a, real_x, real_y, real_z]
    variable_q: Quat = (real_a, real_x, real_y, real_z)

    def derivative(value: Quat, variable: s.Symbol) -> Quat:
        return tuple(s.diff(component, variable) for component in value)  # type: ignore

    def laplacian(value: Quat) -> Quat:
        return tuple(sum(s.diff(component, v, 2) for v in variables) for component in value)  # type: ignore

    def fueter(value: Quat) -> Quat:
        return add(*(mul(unit, derivative(value, v)) for unit, v in zip(basis, variables)))

    c.quat("Fueter(q)=-2", fueter(variable_q), scale(-2, ONE))
    c.quat("Laplacian(q^2)=-4", laplacian(power(variable_q, 2)), scale(-4, ONE))
    cubic_lap = scale(-4, (3*real_a, real_x, real_y, real_z))
    c.quat("Laplacian(q^3)=-4(3a+v)", laplacian(power(variable_q, 3)), cubic_lap)
    for degree in range(1, 7):
        c.quat(f"Fueter(Laplacian(q^{degree}))=0", fueter(laplacian(power(variable_q, degree))), ZERO)
    return c


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "verification.json")
    args = parser.parse_args()
    checks = run_checks()
    failed = sum(not item["passed"] for item in checks.records)
    report = {
        "description": "Exact finite symbolic checks; not a formal verification of the article.",
        "python_version": sys.version.split()[0],
        "sympy_version": s.__version__,
        "check_groups": len(checks.records),
        "scalar_identities": sum(item["scalar_identities"] for item in checks.records),
        "passed_groups": len(checks.records)-failed,
        "failed_groups": failed,
        "limitations": [
            "No construction of the surreal numbers is machine-checked.",
            "No general Hahn summability theorem is machine-checked.",
            "No proof of the Berarducci-Mantova derivation properties is supplied by this script.",
            "No general analytic or spectral theorem is established by finitely many symbolic checks.",
        ],
        "checks": checks.records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(f"\n{len(checks.records)-failed}/{len(checks.records)} groups passed; "
          f"{report['scalar_identities']} scalar identities. Report: {args.output}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
