#!/usr/bin/env python3
"""Exact regressions for the canonical-frame simplification.

These tests supplement, and do not replace, the proofs in canonical_frame.pdf.
Dependencies: Python 3, SymPy, mpmath. All random choices use a fixed seed.
"""
from __future__ import annotations

import math
import random
from fractions import Fraction

import mpmath as mp
import sympy as sp

RNG = random.Random(272611)
COUNTS: dict[str, int] = {}


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    COUNTS[name] = COUNTS.get(name, 0) + 1


def zero_matrix(a: sp.Matrix) -> bool:
    return all(sp.cancel(x) == 0 for x in a)


def equal(a, b) -> bool:
    return sp.cancel(a - b) == 0


def gaussian_matrix(n: int, m: int, denominator: int = 3) -> sp.Matrix:
    return sp.Matrix(n, m, lambda _a, _b: (
        sp.Rational(RNG.randrange(-2, 3), denominator)
        + sp.I * sp.Rational(RNG.randrange(-2, 3), denominator)
    ))


def positive(a: sp.Matrix) -> bool:
    """Sylvester's criterion, with exact rational minors."""
    return zero_matrix(a - a.H) and all(
        sp.simplify(a[:j, :j].det()).is_positive is True
        for j in range(1, a.rows + 1)
    )


def check_block_identities() -> None:
    for k, i in [(1, 0), (1, 1), (2, 1), (2, 2), (4, 2), (7, 1), (7, 3)]:
        for _ in range(3):
            t = gaussian_matrix(i + 1, i + 1)
            hmat = sp.simplify(sp.eye(i + 1) + t.H * t)
            a, b, h = hmat[:i, :i], hmat[:i, i:], hmat[i, i]
            x, v = gaussian_matrix(k, i), gaussian_matrix(k, 1)
            schur = sp.simplify(a - b * b.H / h)
            c = sp.simplify(h + (v.H * v)[0, 0])
            u = sp.simplify(x - v * b.H / h)
            p = sp.simplify(sp.eye(k) - v * v.H / c)
            g = sp.simplify(sp.eye(k) + v * v.H / h)
            q = hmat + sp.Matrix.hstack(x, v).H * sp.Matrix.hstack(x, v)
            check("positive Schur complement", positive(schur))
            check("rank-one inverse", zero_matrix(p * g - sp.eye(k)))
            check("Schur determinant", equal(hmat.det(), h * schur.det()))
            check("rank-one determinant", equal(g.det(), c / h))
            check("bordered determinant", equal(q.det(), c * (schur + u.H * p * u).det()))
            check("Sylvester determinant form", equal(
                q.det(), hmat.det() * (g + u * schur.inv() * u.H).det()))
            jacobian = p.det() ** (-i) * schur.det() ** k
            old = (c * schur.det()) ** (-(k + i)) * jacobian
            new = hmat.det() ** (-i) * c ** (-k)
            check("complex Jacobian cancellation", equal(old, new))


def shape(r: int, k: int):
    n = 2 * r + k + 1
    j = sp.zeros(n)
    z = r + k
    for a in range(r):
        j[a, z + 1 + a] = j[z + 1 + a, a] = 1
    for a in range(r, r + k):
        j[a, a] = 1
    j[z, z] = -1
    f = sp.eye(n)[:, list(range(r)) + [z]]
    e = sp.eye(n)[:, list(range(r, r + k))]
    return j, f, e, z


def unitary_cayley(j: sp.Matrix, active: list[int]) -> sp.Matrix:
    """Rational J-unitary matrix from a J-skew-adjoint Cayley parameter."""
    n = j.rows
    while True:
        raw = sp.zeros(n)
        block = gaussian_matrix(len(active), len(active), denominator=11)
        for a, aa in enumerate(active):
            for b, bb in enumerate(active):
                raw[aa, bb] = block[a, b]
        skew = raw - raw.H
        c = j * skew
        if (sp.eye(n) - c).det() != 0:
            g = sp.simplify((sp.eye(n) - c).inv() * (sp.eye(n) + c))
            check("Cayley unitarity", zero_matrix(g.H * j * g - j))
            return g


def check_geometry() -> None:
    # Lower floors have gamma fixing z and the unused isotropic tail.
    # Top floors allow a fully general gamma. No scalar test assumes k >= 7.
    for r, k, i, lower in [(1, 1, 0, True), (1, 1, 1, True),
                            (2, 1, 1, True), (1, 2, 1, False)]:
        j, f, e, z = shape(r, k)
        n = j.rows
        y = unitary_cayley(j, list(range(n)))
        active = list(range(i)) + list(range(r, r + k)) + list(range(z + 1, z + 1 + i))
        if not lower:
            active = list(range(n))
        idx = list(range(i)) + [r]
        fs = f[:, idx]
        while True:
            gamma = unitary_cayley(j, active)
            zmat = sp.simplify(f.H * j * gamma * f)
            bmat = zmat.extract(idx, idx)
            if bmat.det() != 0:
                break
        neg = (sp.eye(n) - j) * f
        left = sp.simplify((neg.H * y.inv() * f).inv() * neg.H * y.inv())
        dual = sp.simplify(zmat[:, idx] * bmat.inv())
        omega = sp.simplify(j * left.H * dual)
        image = sp.simplify(gamma * fs * bmat.inv())
        diff = sp.simplify(image - omega)
        v = sp.simplify(e.H * diff)
        hmat = sp.simplify(-omega.H * j * omega)
        w = sp.simplify(y.inv() * omega)
        u = sp.simplify(y.inv() * fs)
        kmat = sp.simplify(omega.H * j * image)
        check("canonical subframe duality", zero_matrix(fs.H * j * omega - sp.eye(i + 1)))
        check("canonical negative space", zero_matrix(j * w + w))
        check("canonical positive Gram", positive(hmat))
        check("difference orthogonal to full frame", zero_matrix(f.H * j * diff))
        check("quotient Gram identity", zero_matrix(v.H * v - diff.H * j * diff))
        check("dual Euclidean Gram", zero_matrix(u.H * w + sp.eye(i + 1)))
        check("Ostrowski expansion", zero_matrix(
            -kmat - kmat.H - hmat - v.H * v + image.H * j * image))
        nu_sq = sp.simplify(abs((left * gamma * f).det()) ** 2)
        reduced_sq = sp.simplify(abs(bmat.det()) ** 2 * abs(kmat.det()) ** 2)
        check("reduced volume identity", equal(nu_sq, reduced_sq))
        det_bound = sp.simplify((u.H * u).det() * hmat.det() - 1)
        check("determinant Cauchy Schwarz", det_bound.is_nonnegative is True)
        if lower:
            last = sp.simplify(hmat[i, i] + (v[:, i:].H * v[:, i:])[0, 0])
            check("lower-floor last column equals one", equal(last, 1))
        if i == r:
            # The top-floor certificate with u_Bessel = 1: using Frobenius
            # norm of y^-1 is weaker than operator norm, but remains valid.
            theta_sq = sp.simplify(sp.trace(y.inv().H * y.inv()))
            check("top-floor last-column lower bound", (
                sp.simplify(theta_sq * hmat[i, i] - 1).is_nonnegative is True))


def check_constants_and_integrals() -> None:
    # pi < 22/7 supplies a rational certificate for C_{k,i} <= 1.
    for k in range(7, 31):
        for i in range(0, 21):
            bound = Fraction(1)
            for r in range(i):
                bound *= Fraction(22, 7) ** k * Fraction(math.factorial(r), math.factorial(k + r))
            check("rational Hua constant upper bound", 0 < bound <= 1)
    mp.mp.dps = 60
    # k=i=1, h=3, v=2, b=1, A=2: detH=5, c=7.
    # Translating X removes b. A radial one-complex-variable integral then
    # evaluates the nontrivial bordered identity independently of determinants.
    h, v, schur = mp.mpf(3), mp.mpf(2), mp.mpf(5) / 3
    c = h + v * v
    p = h / c
    measured = mp.quad(lambda r: 2 * mp.pi * r / (c * (schur + p * r * r)) ** 2, [0, 1, mp.inf])
    predicted = mp.pi / 35
    check("radial bordered integral", abs(measured - predicted) < mp.mpf("1e-50"))
    print("Radial test absolute error:", mp.nstr(abs(measured - predicted), 8))
    # Nonempty border is essential: integrating every i+1 column at the
    # proposed exponent k+i diverges. The report preserves the fixed column.
    for k, i in [(7, 0), (7, 1), (7, 4), (12, 3)]:
        for rho, theta, delta in [(2, 3, 5), (1, 1, 2)]:
            for j_minus_i in [0, 1]:
                a = sp.Rational(2) ** ((i + 1) * (k + i)) * sp.Rational(rho) ** (2 * i * (i + 1))
                a *= sp.Rational(theta) ** (2 * k * j_minus_i) / sp.Rational(delta) ** (k + i)
                b = (2 * sp.Rational(rho) ** 2) ** ((i + 1) * i)
                b *= (sp.Rational(2) ** (i + 1) * sp.Rational(theta) ** (2 * j_minus_i)) ** k
                b /= sp.Rational(delta) ** (k + i)
                check("exact published constant", equal(a, b))


if __name__ == "__main__":
    check_block_identities()
    check_geometry()
    check_constants_and_integrals()
    for name, count in COUNTS.items():
        print(f"PASS {count:4d}  {name}")
    print(f"PASS TOTAL {sum(COUNTS.values())} checks; seed 272611")
