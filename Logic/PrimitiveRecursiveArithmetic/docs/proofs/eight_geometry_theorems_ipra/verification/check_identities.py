#!/usr/bin/env python3
"""Exact symbolic audit for the constructive geometry report.

This script is deliberately independent of Lean and of the iPRA proof layer.
It checks the fixed polynomial identities used in the human proofs with SymPy's
exact integer/rational expression engine.  It performs no numerical sampling.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Iterable

import sympy as sp


@dataclass
class Audit:
    passed: list[str]

    def zero(self, name: str, value: sp.Expr | sp.MatrixBase | Iterable[sp.Expr]) -> None:
        if isinstance(value, sp.MatrixBase):
            items = list(value)
        elif isinstance(value, (list, tuple)):
            items = list(value)
        else:
            items = [value]
        residues = [sp.expand(x) for x in items]
        if any(x != 0 for x in residues):
            raise AssertionError(f"{name}: nonzero residue(s): {residues}")
        self.passed.append(name)

    def equal(self, name: str, left, right) -> None:
        if isinstance(left, sp.MatrixBase) or isinstance(right, sp.MatrixBase):
            self.zero(name, sp.Matrix(left) - sp.Matrix(right))
        else:
            self.zero(name, sp.expand(left - right))


def cross(u: sp.Matrix, v: sp.Matrix) -> sp.Matrix:
    return sp.Matrix(
        [
            u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0],
        ]
    )


def det_cols(u: sp.Matrix, v: sp.Matrix, w: sp.Matrix) -> sp.Expr:
    return sp.Matrix.hstack(u, v, w).det()


def bracket2(p: sp.Matrix, q: sp.Matrix) -> sp.Expr:
    return p[0] * q[1] - p[1] * q[0]


def pappus_harmonic(audit: Audit) -> None:
    t, d = sp.symbols("t d")
    A = sp.Matrix([0, 0, 1])
    B = sp.Matrix([1, 0, 1])
    Z = sp.Matrix([0, 1, 1])
    Y = sp.Matrix([t, 0, 1])
    D = sp.Matrix([0, d, 1])

    C = cross(cross(D, Y), cross(Z, B))
    X = cross(cross(A, C), cross(D, B))
    W = cross(cross(Z, X), cross(A, B))

    audit.equal(
        "Pappus harmonic: C coordinate",
        C,
        sp.Matrix([t * (d - 1), -d * (t - 1), d - t]),
    )
    audit.equal(
        "Pappus harmonic: X coordinate",
        X,
        sp.Matrix(
            [-d * t * (d - 1), d**2 * (t - 1), -d * (d * t - 2 * t + 1)]
        ),
    )
    audit.equal(
        "Pappus harmonic: W proportional coordinate",
        W,
        -d * (d - 1) * sp.Matrix([t, 0, 2 * t - 1]),
    )

    A1 = sp.Matrix([0, 1])
    B1 = sp.Matrix([1, 1])
    Y1 = sp.Matrix([t, 1])
    W1 = sp.Matrix([t, 2 * t - 1])
    audit.zero(
        "Pappus harmonic: division-free cross-ratio -1",
        bracket2(A1, W1) * bracket2(B1, Y1)
        + bracket2(A1, Y1) * bracket2(B1, W1),
    )


def ceva_menelaus(audit: Audit) -> None:
    dB, dC, eA, eC, fA, fB = sp.symbols("dB dC eA eC fA fB")
    AD = sp.Matrix([0, -dC, dB])
    BE = sp.Matrix([eC, 0, -eA])
    CF = sp.Matrix([-fB, fA, 0])
    ceva_det = sp.Matrix.hstack(AD, BE, CF).det()
    # Transposing a 3x3 matrix does not change its determinant.
    audit.equal(
        "Ceva: determinant expansion",
        ceva_det,
        dB * eC * fA - dC * eA * fB,
    )

    P = sp.Matrix([eA * dC, dB * eC, dC * eC])
    audit.zero("Ceva: witness on AD", AD.dot(P))
    audit.zero("Ceva: witness on BE", BE.dot(P))
    audit.equal(
        "Ceva: third incidence residue is hypothesis",
        CF.dot(P),
        dB * eC * fA - dC * eA * fB,
    )

    D = sp.Matrix([0, dB, dC])
    E = sp.Matrix([eA, 0, eC])
    F = sp.Matrix([fA, fB, 0])
    men_det = det_cols(D, E, F)
    audit.equal(
        "Menelaus: determinant expansion",
        men_det,
        dB * eC * fA + dC * eA * fB,
    )
    line_DE = cross(D, E)
    audit.equal(
        "Menelaus: explicit line incidence residue",
        line_DE.dot(F),
        dB * eC * fA + dC * eA * fB,
    )


def carnot_conic(audit: Audit) -> None:
    v0, p0, w0, y1, z1, y2, z2 = sp.symbols("v p w y1 z1 y2 z2")
    h1 = v0 * y1**2 + p0 * y1 * z1 + w0 * z1**2
    h2 = v0 * y2**2 + p0 * y2 * z2 + w0 * z2**2
    delta = y1 * z2 - y2 * z1
    audit.equal(
        "Binary quadratic: subtraction factorization",
        y2 * z2 * h1 - y1 * z1 * h2,
        delta * (v0 * y1 * y2 - w0 * z1 * z2),
    )

    d1, d2, e1, e2, a1, a2, c1, c2, p1, p2, q1, q2 = sp.symbols(
        "d1 d2 e1 e2 a1 a2 c1 c2 p1 p2 q1 q2"
    )
    x, y, z = sp.symbols("x y z")
    Dy, Dz = d1 * d2, e1 * e2
    Ex, Ez = a1 * a2, c1 * c2
    Fx, Fy = p1 * p2, q1 * q2

    u = Dy * Ez * Fy
    v = Dz * Ex * Fy
    w = Dy * Ex * Fy
    s = -Ex * Fy * (e1 * d2 + d1 * e2)
    t = -Dy * Fy * (c1 * a2 + a1 * c2)
    r = -Dy * Ez * (q1 * p2 + p1 * q2)
    Q = u * x**2 + v * y**2 + w * z**2 + s * y * z + t * z * x + r * x * y

    audit.equal(
        "Carnot conic: BC factorization",
        Q.subs(x, 0),
        Ex * Fy * (e1 * y - d1 * z) * (e2 * y - d2 * z),
    )
    audit.equal(
        "Carnot conic: CA factorization",
        Q.subs(y, 0),
        Dy * Fy * (c1 * x - a1 * z) * (c2 * x - a2 * z),
    )
    ab_factor = Dy * Ez * (q1 * x - p1 * y) * (q2 * x - p2 * y)
    audit.equal(
        "Carnot conic: AB residue equals product-condition residue",
        Q.subs(z, 0) - ab_factor,
        (Dz * Ex * Fy - Dy * Ez * Fx) * y**2,
    )


def carnot_polygon(audit: Audit) -> None:
    c0 = sp.symbols("c")
    for n in (1, 2, 3, 4, 5):
        ts = sp.symbols(f"t1:{n+1}")
        T = sp.prod(ts)
        U = sp.prod(1 - q for q in ts)
        g0 = c0 * sp.prod(-q for q in ts)
        g1 = c0 * U
        audit.zero(
            f"Carnot polygon: endpoint identity for {n} certified roots",
            g1 * T - ((-1) ** n) * g0 * U,
        )


def hoehn(audit: Audit) -> None:
    xs = sp.symbols("x0:5")
    ys = sp.symbols("y0:5")
    points = [sp.Matrix([xs[i], ys[i], 1]) for i in range(5)]

    def delta(i: int, j: int, k: int) -> sp.Expr:
        return det_cols(points[i % 5], points[j % 5], points[k % 5])

    A: list[sp.Expr] = []
    B: list[sp.Expr] = []
    S: list[sp.Expr] = []
    C: list[sp.Expr] = []
    D: list[sp.Expr] = []
    T: list[sp.Expr] = []
    for i in range(5):
        Ai = delta(i - 1, i + 1, i)
        Bi = -delta(i - 1, i + 1, i + 2)
        Ci = delta(i + 1, i + 3, i)
        Di = -delta(i + 1, i + 3, i + 2)
        A.append(Ai)
        B.append(Bi)
        S.append(Ai + Bi)
        C.append(Ci)
        D.append(Di)
        T.append(Ci + Di)

    for i in range(5):
        audit.zero(f"Hoehn: D[{i}] = -A[{(i+2)%5}]", D[i] + A[(i + 2) % 5])
        audit.zero(f"Hoehn: C[{i}] = -B[{(i-1)%5}]", C[i] + B[(i - 1) % 5])
        audit.zero(f"Hoehn: T[{i}] = -S[{(i+1)%5}]", T[i] + S[(i + 1) % 5])

    # Expanding the full ten-variable coordinate products is needlessly large.
    # After the determinant identities above are certified, the remaining
    # cancellation is a formal commutative-ring identity in fifteen atoms.
    AA = sp.symbols("A0:5")
    BB = sp.symbols("B0:5")
    SS = sp.symbols("S0:5")
    CC = [-BB[(i - 1) % 5] for i in range(5)]
    DD = [-AA[(i + 2) % 5] for i in range(5)]
    TT = [-SS[(i + 1) % 5] for i in range(5)]
    audit.zero(
        "Hoehn: first quotient-free five-factor certificate",
        sp.prod(AA[i] * TT[i] for i in range(5))
        - sp.prod(SS[i] * DD[i] for i in range(5)),
    )
    audit.zero(
        "Hoehn: second quotient-free five-factor certificate",
        sp.prod(CC[i] * SS[i] for i in range(5))
        - sp.prod(TT[i] * BB[i] for i in range(5)),
    )


def pappus_hexagon(audit: Audit) -> None:
    a, b, c, d, e, f = sp.symbols("a b c d e f")
    A = sp.Matrix([a, 1, 0])
    B = sp.Matrix([b, 1, 0])
    C = sp.Matrix([c, 1, 0])
    D = sp.Matrix([d, 0, 1])
    E = sp.Matrix([e, 0, 1])
    F = sp.Matrix([f, 0, 1])
    X = cross(cross(A, E), cross(B, D))
    Y = cross(cross(A, F), cross(C, D))
    Z = cross(cross(B, F), cross(C, E))
    audit.equal(
        "Pappus hexagon: X coordinate",
        X,
        sp.Matrix([a * d - b * e, d - e, a - b]),
    )
    audit.equal(
        "Pappus hexagon: Y coordinate",
        Y,
        sp.Matrix([a * d - c * f, d - f, a - c]),
    )
    audit.equal(
        "Pappus hexagon: Z coordinate",
        Z,
        sp.Matrix([b * e - c * f, e - f, b - c]),
    )
    audit.zero("Pappus hexagon: X - Y + Z", X - Y + Z)
    audit.zero("Pappus hexagon: collinearity determinant", det_cols(X, Y, Z))


def pascal_brianchon(audit: Audit) -> None:
    a, b, c, d, e, f = sp.symbols("a b c d e f")

    def secant(s, t) -> sp.Matrix:
        return sp.Matrix([1, -(s + t), s * t])

    X = cross(secant(a, b), secant(d, e))
    Y = cross(secant(b, c), secant(e, f))
    Z = cross(secant(c, d), secant(f, a))
    audit.zero(
        "Pascal: weighted vector certificate",
        (c - f) * X + (d - a) * Y + (e - b) * Z,
    )
    audit.zero("Pascal: collinearity determinant", det_cols(X, Y, Z))

    def point(t) -> sp.Matrix:
        return sp.Matrix([t**2, t, 1])

    def tangent(t) -> sp.Matrix:
        return sp.Matrix([1, -2 * t, t**2])

    for name, q in zip("abcdef", (a, b, c, d, e, f)):
        audit.zero(f"Standard conic: point {name} lies on xz-y^2", point(q)[0] * point(q)[2] - point(q)[1] ** 2)
        audit.zero(f"Standard conic: tangent {name} is incident", tangent(q).dot(point(q)))

    lines = [tangent(q) for q in (a, b, c, d, e, f)]
    vertices = [cross(lines[i], lines[(i + 1) % 6]) for i in range(6)]
    diagonals = [
        cross(vertices[0], vertices[3]),
        cross(vertices[1], vertices[4]),
        cross(vertices[2], vertices[5]),
    ]
    audit.zero(
        "Brianchon: standard-conic diagonal concurrency determinant",
        det_cols(diagonals[0], diagonals[1], diagonals[2]),
    )


def main() -> int:
    audit = Audit([])
    checks = [
        pappus_harmonic,
        ceva_menelaus,
        carnot_conic,
        carnot_polygon,
        hoehn,
        pappus_hexagon,
        pascal_brianchon,
    ]
    try:
        for check in checks:
            check(audit)
    except Exception as exc:  # produce a useful CI-style failure
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

    print(f"SymPy version: {sp.__version__}")
    print(f"Exact checks passed: {len(audit.passed)}")
    for name in audit.passed:
        print(f"PASS  {name}")
    print("ALL CERTIFICATES PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
