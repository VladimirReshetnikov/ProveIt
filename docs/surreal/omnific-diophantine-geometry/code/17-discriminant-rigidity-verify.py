#!/usr/bin/env python3
"""Exact finite checks for article.tex; NOT a proof of the Hahn/etale theorems.

Requires Python 3.10+ and SymPy 1.14.0 (the version used for the delivered run).
Writes only the path explicitly supplied by --output (default verification.json).
The random seed is fixed and every arithmetic comparison is exact.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
import random
from collections import Counter
from pathlib import Path
from typing import Iterable

import sympy as sp

X, Y, T, s, u, a, b, alpha, beta = sp.symbols("X Y T s u a b alpha beta")
COUNTS: Counter[str] = Counter()
RNG = random.Random(20260923)


def check(condition: bool, group: str, description: str) -> None:
    if not bool(condition):
        raise AssertionError(f"[{group}] {description}")
    COUNTS[group] += 1


def equal(left: sp.Expr, right: sp.Expr, group: str, description: str) -> None:
    check(sp.cancel(left - right) == 0, group, description)


def elementary(values: Iterable[sp.Expr]) -> list[sp.Expr]:
    """Return e_0,...,e_m by a finite exact recurrence."""
    coeff = [sp.Integer(1)]
    for val in values:
        coeff.append(sp.Integer(0))
        for j in range(len(coeff) - 1, 0, -1):
            coeff[j] = sp.cancel(coeff[j] + val * coeff[j - 1])
    return coeff


def translation_checks() -> None:
    for n in range(1, 7):
        for rep in range(4):
            roots = RNG.sample(range(-12, 13), n)
            p0 = sp.prod(X - r for r in roots).expand()
            h = (rep + 1) * s + (rep - 1) * s**2
            p = p0.subs(X, X - h).expand()
            a1 = sp.Poly(p, X).coeff_monomial(X ** (n - 1))
            recovered = -(a1 - a1.subs(s, 0)) / n
            equal(recovered, h, "translation", f"degree {n}: extracted shift")
            equal(p.subs(s, 0), p0, "translation", "constant extraction")
            equal(p.subs(X, X + h), p0, "translation", "inverse substitution")
            equal(p.subs(X, h + 3), p0.subs(X, 3), "translation", "marked value")
            delta0 = sp.prod((ri - rj)**2 for ri, rj in itertools.combinations(roots, 2))
            if n <= 5:
                equal(sp.discriminant(p, X), delta0, "discriminants", f"degree {n}")
            if n >= 2:
                q0 = sp.prod(X - r for r in roots[: n // 2]).expand()
                r0 = sp.div(p0, q0, X)[0]
                equal(q0.subs(X, X - h) * r0.subs(X, X - h), p,
                      "factorization", "translated monic factors")
    p0 = X**3 - 2 * X + 1
    equal(sp.discriminant(p0, X), 5, "examples", "article cubic discriminant")


def root_velocity_checks() -> None:
    # The test uses exact rational roots and freely varied coefficient velocities.
    for n in range(2, 7):
        for rep in range(6):
            roots = list(map(sp.Integer, RNG.sample(range(-15, 16), n)))
            p = sp.prod(X - r for r in roots).expand()
            pp = sp.diff(p, X)
            bs = [sp.Integer(RNG.randint(-5, 5)) for _ in range(n)]
            q = sum(bs[j] * X ** (n - 1 - j) for j in range(n))
            slopes = [sp.cancel(-q.subs(X, r) / pp.subs(X, r)) for r in roots]
            delta = sp.discriminant(p, X)
            vals = []
            for i, j in itertools.combinations(range(n), 2):
                ri, rj = roots[i], roots[j]
                w = sp.cancel((slopes[i] - slopes[j]) / (ri - rj))
                sij = sp.cancel((q.subs(X, rj) * pp.subs(X, ri)
                                 - q.subs(X, ri) * pp.subs(X, rj)) / (ri - rj))
                equal(w, sij / (pp.subs(X, ri) * pp.subs(X, rj)),
                      "velocity_certificate", "divided-difference identity")
                cleared = (sij * sp.prod(pp.subs(X, roots[l]) for l in range(n) if l != i)
                           * sp.prod(pp.subs(X, roots[l]) for l in range(n) if l != j))
                equal(delta**2 * w, cleared, "velocity_certificate", "Delta squared clears denominators")
                vals.append(w)
            es = elementary(vals)
            scaled = elementary([3 * w for w in vals])
            reversed_es = elementary(reversed(vals))
            for j in range(len(es)):
                equal(scaled[j], 3**j * es[j], "velocity_symmetry", "homogeneity in coefficient velocity")
                equal(reversed_es[j], es[j], "velocity_symmetry", "edge permutation invariance")
            char = sp.prod(T - w for w in vals).expand()
            equal(char, sum((-1)**j * es[j] * T**(len(vals) - j) for j in range(len(es))),
                  "velocity_symmetry", "velocity characteristic polynomial")
            # Direct symbolic discriminant differentiation is limited to n<=4.
            if n <= 4 and rep < 2:
                delta_s = sp.discriminant(p + s * q, X)
                equal(sp.diff(delta_s, s).subs(s, 0), 2 * delta * es[1],
                      "velocity_trace", "D Delta = 2 Delta sum velocities")
    disc = a*a - 4*b
    numerator = a*alpha - 2*beta
    equal(sp.diff(disc, a)*alpha + sp.diff(disc, b)*beta, 2*numerator,
          "quadratic_certificate", "quadratic discriminant derivative")
    equal(disc**2 * (numerator/disc), disc*numerator,
          "quadratic_certificate", "F_2_1 normalization")


def resultant_and_critical_checks() -> None:
    for n in range(1, 5):
        p0 = sp.prod(X - j for j in range(n)).expand()
        q0 = (X + 7) * (X + 9)
        h = s + s*s
        equal(sp.resultant(p0.subs(X, X-h), q0.subs(X, X-h), X),
              sp.resultant(p0, q0, X), "resultants", "common shift invariance")
        resultant = sp.resultant(p0.subs(X, X-s), q0, X)
        check(sp.degree(resultant, s) == 2*n, "resultants", "degree of relative-shift resultant")
    for d in range(2, 8):
        f0 = X**d + 2*X**(d-1) - 3*X + 5
        h, c = s+s*s, 3*s-s**3
        f = f0.subs(X, X-h).expand() + c
        equal(sp.diff(f, X), sp.diff(f0, X).subs(X, X-h),
              "critical", "critical-polynomial translation")
        equal(f.subs(X, h)-f0.subs(X, 0), c, "critical", "target-shift extraction")
        a1 = sp.Poly(f, X).coeff_monomial(X**(d-1))
        equal(-(a1-a1.subs(s, 0))/d, h, "critical", "source-shift extraction")
    equal(sp.discriminant(X**3-X, X), 4, "examples", "quartic critical discriminant")


def matrix_and_boundary_checks() -> None:
    rotation = sp.Matrix([[sp.Rational(3, 5), -sp.Rational(4, 5)],
                          [sp.Rational(4, 5), sp.Rational(3, 5)]])
    cmat = rotation * sp.diag(-2, 3) * rotation.T
    h = s+s*s
    mat = cmat + h*sp.eye(2)
    equal((mat*mat.T-mat.T*mat).norm(), 0, "matrices", "normal shifted matrix")
    eigenvalues = [-2, 3]
    projectors = []
    for ci in eigenvalues:
        cj = eigenvalues[1-eigenvalues.index(ci)]
        e = (mat - (h+cj)*sp.eye(2))/(ci-cj)
        check(e*e == e, "matrices", "idempotent")
        check(e.T == e, "matrices", "Hermitian")
        check(not any(entry.has(s) for entry in e), "matrices", "constant projection")
        projectors.append(e)
    check(sum(projectors, sp.zeros(2)) == sp.eye(2), "matrices", "projection sum")
    equal(sp.discriminant(mat.charpoly(X).as_expr(), X), 25,
          "matrices", "constant spectral discriminant")
    triangular = sp.Matrix([[0, s], [0, 1]])
    equal(sp.discriminant(triangular.charpoly(X).as_expr(), X), 1,
          "counterexamples", "nonnormal constant discriminant")
    check(triangular*triangular.T-triangular.T*triangular != sp.zeros(2),
          "counterexamples", "normality fails")
    r = sp.symbols("r")
    relation = r*r-s*r+1/s  # r(s-r)=1/s, with s infinite in the article.
    full_disc = sp.discriminant(X*(X-s)*(X-r), X)
    equal(sp.rem(full_disc-1, relation, r), 0,
          "counterexamples", "two-sided Hahn discriminant one")
    equal(sp.discriminant(X*X*(X-s), X), 0,
          "counterexamples", "zero-discriminant family")
    for p in (2, 3, 5):
        poly = X**(p*p) + s*X**p + X
        derivative = sp.Poly(sp.diff(poly, X), X, s, modulus=p)
        check(derivative.as_expr() == 1, "positive_characteristic", "derivative is one")
        shift = sp.Poly((X-u)**(p*p) + X-u, X, u, modulus=p)
        check(all(monomial[0] != p for monomial, coeff in shift.terms()),
              "positive_characteristic", "translated constant polynomial has no X^p term")
        if p in (2, 3):
            delta = sp.Poly(sp.discriminant(poly, X), s, modulus=p)
            check(delta.degree() == 0 and delta.as_expr() != 0,
                  "positive_characteristic", "nonzero constant discriminant")
    relation_etale = Y*Y-s*s-1
    equal(sp.rem((s+Y)*(Y-s)-1, relation_etale, Y), 0,
          "counterexamples", "nonetale algebra moving unit inverse")
    equal(sp.discriminant(relation_etale, Y), 4*(s*s+1),
          "counterexamples", "nonetale algebra nonunit discriminant")
    equal((s+Y)-(Y-s), 2*s, "counterexamples", "moving unit detects transcendental parameter")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    translation_checks()
    root_velocity_checks()
    resultant_and_critical_checks()
    matrix_and_boundary_checks()
    report = {
        "status": "passed",
        "arithmetic": "exact rational and symbolic polynomial arithmetic; finite-field reductions",
        "seed": 20260923,
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "assertions": sum(COUNTS.values()),
        "assertions_by_group": dict(sorted(COUNTS.items())),
        "scope": "Finite identities and examples only. Not formal verification of arbitrary Hahn supports, all degrees, finite etale descent, or the mathematical manuscript.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
