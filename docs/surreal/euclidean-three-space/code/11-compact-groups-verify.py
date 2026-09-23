#!/usr/bin/env python3
"""Finite algebra checks accompanying article.tex.

These are exact smoke tests, not a verification of the class-theoretic or
Nash implicit-function arguments. Requires Python 3.10+ and SymPy 1.12+.
Run: python verify.py [--output verification_results.json]
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from pathlib import Path
from typing import Any

import sympy as sp


def require(condition: bool, name: str, checks: list[dict[str, Any]],
            details: Any = None) -> None:
    """Raise explicitly (also under python -O) when a check fails."""
    passed = bool(condition)
    entry: dict[str, Any] = {"name": name, "passed": passed}
    if details is not None:
        entry["details"] = details
    checks.append(entry)
    if not passed:
        raise AssertionError(f"FAILED: {name}")


def zero_matrix(matrix: sp.MatrixBase) -> bool:
    return all(sp.cancel(value) == 0 for value in matrix)


def bracket(x: sp.MatrixBase, y: sp.MatrixBase) -> sp.Matrix:
    return sp.Matrix(x * y - y * x)


def real_vector(matrix: sp.MatrixBase) -> sp.Matrix:
    """Encode a complex matrix as a real vector, using exact real/imag parts."""
    values = list(matrix)
    return sp.Matrix([sp.simplify(sp.re(x)) for x in values]
                     + [sp.simplify(sp.im(x)) for x in values])


def span_certificate(basis: list[sp.Matrix], vectors: list[sp.Matrix],
                     labels: list[str]) -> dict[str, Any]:
    ambient_basis = sp.Matrix.hstack(*(real_vector(x) for x in basis))
    candidates = sp.Matrix.hstack(*(real_vector(x) for x in vectors))
    _, pivots = candidates.rref()
    chosen = list(pivots[:len(basis)])
    if len(chosen) != len(basis):
        return {"rank": len(pivots), "dimension": len(basis), "determinant": "0"}
    coordinate_columns = [ambient_basis.gauss_jordan_solve(candidates[:, j])[0]
                          for j in chosen]
    coordinates = sp.Matrix.hstack(*coordinate_columns)
    return {
        "rank": candidates.rank(),
        "dimension": len(basis),
        "chosen_columns": [labels[j] for j in chosen],
        "coordinate_matrix": [[str(x) for x in row] for row in coordinates.tolist()],
        "determinant": str(sp.factor(coordinates.det())),
    }


def permutation_sign(p: tuple[int, ...]) -> int:
    inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p)))
    return -1 if inversions % 2 else 1


def truncate_total(poly: sp.Expr, variables: tuple[sp.Symbol, ...], degree: int) -> sp.Expr:
    data = sp.Poly(sp.expand(poly), *variables)
    return sp.Add(*(coefficient * sp.prod(v**e for v, e in zip(variables, exponents))
                    for exponents, coefficient in data.terms()
                    if sum(exponents) <= degree))


def run_checks() -> list[dict[str, Any]]:
    checks: list[dict[str, Any]] = []
    a, c = sp.symbols("a c", nonzero=True)
    b = sp.symbols("b")
    I2 = sp.eye(2)
    u = lambda x: sp.Matrix([[1, x], [0, 1]])
    ell = lambda x: sp.Matrix([[1, 0], [x, 1]])
    w = u(a) * ell(-1/a) * u(a)
    require(zero_matrix(w - sp.Matrix([[0, a], [-1/a, 0]])),
            "SL2 elementary Weyl factorization", checks)
    wm = u(-1) * ell(1) * u(-1)
    require(zero_matrix(w * wm - sp.diag(a, 1/a)),
            "SL2 elementary diagonal factorization", checks)
    d = sp.diag(c, 1/c)
    require(zero_matrix(d * u(a) * d.inv() - u(c*c*a)),
            "SL2 root scaling by a square", checks)
    require(zero_matrix(u(a) * u(b) - u(a+b)),
            "SL2 additive root subgroup", checks)
    require(zero_matrix(u(a).inv() - u(-a)),
            "SL2 root subgroup inverse", checks)
    g, h = u(a) * ell(b), ell(c) * u(a)
    require(zero_matrix(g*h*g.inv()*h.inv()-I2
                        - (g*h-h*g)*g.inv()*h.inv()),
            "Exact matrix commutator difference identity", checks)

    # so(3), using the cross-product matrix convention.
    J = [sp.Matrix([[0,0,0],[0,0,-1],[0,1,0]]),
         sp.Matrix([[0,0,1],[0,0,0],[-1,0,0]]),
         sp.Matrix([[0,-1,0],[1,0,0],[0,0,0]])]
    require(all(zero_matrix(x.T+x) and x.trace() == 0 for x in J),
            "so3 basis is skew-symmetric and traceless", checks)
    for i in range(3):
        require(zero_matrix(bracket(J[i], J[(i+1)%3]) - J[(i+2)%3]),
                f"so3 cyclic bracket {i+1}", checks)
    pairs = [(i,j) for i in range(3) for j in range(3)]
    cert = span_certificate(J, [bracket(J[i],J[j]) for i,j in pairs],
                            [f"[J{i+1},J{j+1}]" for i,j in pairs])
    require(cert["rank"] == 3 and cert["determinant"] != "0",
            "so3 mixed-word derivative has full span", checks, cert)
    P = sp.Matrix([[0,0,1],[1,0,0],[0,1,0]])
    rotations = [sp.eye(3), P, P*P]
    cert = span_certificate(J,
        [bracket(k*J[0]*k.T, y) for k in rotations for y in J],
        [f"[Ad(P^{i})J1,J{j+1}]" for i in range(3) for j in range(3)])
    require(cert["rank"] == 3 and cert["determinant"] != "0",
            "so3 one-orbit normal-word derivative has full span", checks, cert)

    # An exact real basis for su(3).
    E = lambda i,j: sp.eye(3)[:, i] * sp.eye(3)[j, :]
    su: list[sp.Matrix] = []
    names: list[str] = []
    for i,j in [(0,1),(0,2),(1,2)]:
        su.extend([E(i,j)-E(j,i), sp.I*(E(i,j)+E(j,i))])
        names.extend([f"A{i+1}{j+1}", f"B{i+1}{j+1}"])
    su.extend([sp.I*(E(0,0)-E(1,1)), sp.I*(E(1,1)-E(2,2))])
    names.extend(["H1", "H2"])
    require(all(zero_matrix(x.conjugate().T+x) and x.trace() == 0 for x in su),
            "su3 basis is anti-Hermitian and traceless", checks)
    require(sp.Matrix.hstack(*(real_vector(x) for x in su)).rank() == 8,
            "su3 basis has real rank eight", checks)
    pairs = list(itertools.product(range(8), repeat=2))
    cert = span_certificate(su, [bracket(su[i],su[j]) for i,j in pairs],
                            [f"[{names[i]},{names[j]}]" for i,j in pairs])
    require(cert["rank"] == 8 and cert["determinant"] != "0",
            "su3 mixed-word derivative has full span", checks, cert)
    cos, sin = sp.Rational(3,5), sp.Rational(4,5)
    rotations_su = [sp.eye(3)]
    for i,j in [(0,1),(0,2),(1,2)]:
        k = sp.eye(3)
        k[i,i], k[j,j] = cos, cos
        k[i,j], k[j,i] = -sin, sin
        rotations_su.append(k)
    require(all(zero_matrix(k.conjugate().T*k-sp.eye(3)) and k.det() == 1
                for k in rotations_su),
            "su3 orbit conjugators are exact rational special unitary matrices", checks)
    X = su[6]
    cert = span_certificate(su,
        [bracket(k*X*k.conjugate().T,y) for k in rotations_su for y in su],
        [f"[Ad(K{i})H1,{names[j]}]" for i in range(len(rotations_su)) for j in range(8)])
    require(cert["rank"] == 8 and cert["determinant"] != "0",
            "su3 fixed-vector adjoint-orbit normal-word derivative has full span", checks, cert)

    # Rational Cayley maps, not an asserted global surreal exponential.
    aa, bb = sp.symbols("alpha beta", real=True)
    cayley = lambda x: (sp.eye(3)-x/2).inv()*(sp.eye(3)+x/2)
    A, B = cayley(aa*J[0]), cayley(bb*J[1])
    require(zero_matrix(A.T*A-sp.eye(3)) and sp.factor(A.det()) == 1,
            "Cayley curve is exactly special orthogonal", checks)
    W = (A*B*A.T*B.T).applyfunc(sp.cancel)
    require(zero_matrix(W.subs(aa,0)-sp.eye(3))
            and zero_matrix(W.subs(bb,0)-sp.eye(3)),
            "Cayley commutator vanishes on both parameter axes", checks)
    mixed = W.diff(aa).diff(bb).subs({aa:0,bb:0})
    require(zero_matrix(mixed-bracket(J[0],J[1])),
            "Normalized mixed Cayley derivative is the Lie bracket", checks)
    require(zero_matrix(W.diff(aa).subs({aa:0,bb:0}))
            and zero_matrix(W.diff(bb).subs({aa:0,bb:0})),
            "Cayley commutator has no first-order term", checks)

    # Finite formal logarithmic identities.
    t = sp.symbols("t", real=True)
    z = (1+sp.I*t)/(1-sp.I*t)
    require(sp.cancel(z*sp.conjugate(z)-1) == 0,
            "Circle Cayley parameter has unit norm", checks)
    u_trunc = sp.series(z-1,t,0,8).removeO()
    log_trunc = sp.Integer(0)
    power = sp.Integer(1)
    for k in range(1,8):
        power = sp.series(power*u_trunc,t,0,8).removeO().expand()
        log_trunc += (-1)**(k+1)*power/sp.Integer(k)
    log_trunc = sp.series(log_trunc,t,0,8).removeO().expand()
    expected = 2*sp.I*(t-t**3/sp.Integer(3)+t**5/sp.Integer(5)-t**7/sp.Integer(7))
    require(sp.expand(log_trunc-expected) == 0,
            "Circle logarithm coefficients through degree seven", checks)
    require(sp.expand(log_trunc+sp.conjugate(log_trunc)) == 0,
            "Truncated circle logarithm is purely imaginary", checks)
    x,y = sp.symbols("x y")
    log1 = lambda z: sum((-1)**(k+1)*z**k/sp.Integer(k) for k in range(1,6))
    remainder = truncate_total(log1(x+y+x*y)-log1(x)-log1(y), (x,y), 5)
    require(remainder == 0,
            "Formal logarithm is additive on products through total degree five", checks)

    # Count monomial matrices combinatorially using exact Gaussian-unit exponents.
    counts: dict[str, list[dict[str, int]]] = {"SO": [], "SU": []}
    for n in range(1,5):
        so_count = 0
        su_count = 0
        for p in itertools.permutations(range(n)):
            sgn = permutation_sign(p)
            for signs in itertools.product([-1,1], repeat=n):
                if sgn * sp.prod(signs) == 1:
                    so_count += 1
            # i**sum(exponents) times the permutation sign equals 1.
            sign_exp = 0 if sgn == 1 else 2
            for exponents in itertools.product(range(4), repeat=n):
                if (sum(exponents)+sign_exp) % 4 == 0:
                    su_count += 1
        expected_so = 2**(n-1)*int(sp.factorial(n))
        expected_su = 4**(n-1)*int(sp.factorial(n))
        require(so_count == expected_so, f"SO omnific monomial count n={n}", checks,
                {"count":so_count,"formula":expected_so})
        require(su_count == expected_su, f"SU omnific monomial count n={n}", checks,
                {"count":su_count,"formula":expected_su})
    return checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("verification_results.json"))
    args = parser.parse_args()
    checks = run_checks()
    payload = {
        "status": "passed",
        "check_count": len(checks),
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "scope": "Finite exact algebra only; not a formal verification of the article.",
        "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2)+"\n", encoding="utf-8")
    print(f"PASS: {len(checks)} exact finite checks. Record: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
