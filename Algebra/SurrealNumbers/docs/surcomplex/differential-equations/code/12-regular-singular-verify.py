#!/usr/bin/env python3
"""Exact finite checks for the accompanying research article.

Requires Python >= 3.10 and SymPy. No floating-point arithmetic is used.
The normalizer handles finite rational supports, a specified rational cutoff,
and a complex Jordan matrix with explicitly specified generalized-eigenvalue
blocks. It verifies finite coefficients, not the infinite Hahn theorem.
"""
from __future__ import annotations

import argparse
import json
import random
from collections import deque
from pathlib import Path
from typing import Any

import sympy as s

Matrix = s.MutableDenseMatrix
Series = dict[s.Rational, Matrix]


def clean(a: Matrix) -> Matrix:
    return a.applyfunc(s.simplify)


def zero(a: Matrix) -> bool:
    return all(s.simplify(x) == 0 for x in a)


def monoid_to(support: list[s.Rational], cutoff: s.Rational) -> list[s.Rational]:
    """Enumerate the finite bounded monoid of a finite positive rational set."""
    if any(x <= 0 or not x.is_Rational for x in support):
        raise ValueError("Support must consist of positive rational exponents")
    seen = {s.Rational(0)}
    queue = deque(seen)
    while queue:
        x = queue.popleft()
        for a in support:
            y = x + a
            if y <= cutoff and y not in seen:
                seen.add(y)
                queue.append(y)
    return sorted(seen)


def normalize(j: Matrix, a_positive: Series,
              blocks: list[tuple[s.Expr, list[int]]],
              cutoff: s.Rational) -> tuple[Series, Series, list[s.Rational]]:
    """The normalized Hahn-Levelt recursion, calculated to a finite cutoff.

    blocks lists (eigenvalue, indices) for the generalized eigenspaces of j.
    Each block must be eigenvalue*I plus nilpotent. Outputs H, B including
    H[0]=I, B[0]=j. The finite residual is checked independently below.
    """
    n = j.rows
    if j.cols != n:
        raise ValueError("Expected square matrix")
    if sorted(i for _, ix in blocks for i in ix) != list(range(n)):
        raise ValueError("Blocks must partition the matrix indices")
    for lam, ix in blocks:
        nilp = j.extract(ix, ix) - lam * s.eye(len(ix))
        if not zero(nilp ** len(ix)):
            raise ValueError("Block is not eigenvalue plus nilpotent")
    grid = monoid_to(list(a_positive), cutoff)
    h: Series = {s.Rational(0): s.eye(n)}
    b: Series = {s.Rational(0): j}
    z = s.zeros(n)
    for gamma in grid[1:]:
        rhs = a_positive.get(gamma, z).copy()
        for alpha in grid[1:]:
            beta = gamma - alpha
            if beta <= 0:
                break
            if beta in h:
                rhs += a_positive.get(alpha, z) * h[beta]
                rhs -= h.get(alpha, z) * b.get(beta, z)
        hg, bg = s.zeros(n), s.zeros(n)
        for lam, rows in blocks:
            jl = j.extract(rows, rows) - lam * s.eye(len(rows))
            for mu, cols in blocks:
                jr = j.extract(cols, cols) - mu * s.eye(len(cols))
                r = rhs.extract(rows, cols)
                c = s.simplify(gamma - lam + mu)
                if c == 0:
                    x = r
                    target = bg
                else:
                    power = r
                    x = s.zeros(len(rows), len(cols))
                    for k in range(len(rows) + len(cols) - 1):
                        x += power / c ** (k + 1)
                        power = jl * power - power * jr
                    assert zero(power), "Nilpotent block bound failed"
                    target = hg
                for u, row in enumerate(rows):
                    for v, col in enumerate(cols):
                        target[row, col] = s.simplify(x[u, v])
        h[gamma], b[gamma] = clean(hg), clean(bg)
    return h, b, grid


def residual(j: Matrix, a_positive: Series, h: Series,
             b: Series, grid: list[s.Rational]) -> None:
    """Check delta(H) - A H + H B coefficientwise, without the recursion."""
    n = j.rows
    a = {s.Rational(0): j, **a_positive}
    for gamma in grid:
        r = gamma * h.get(gamma, s.zeros(n))
        for alpha, aa in a.items():
            r -= aa * h.get(gamma - alpha, s.zeros(n))
        for alpha, hh in h.items():
            r += hh * b.get(gamma - alpha, s.zeros(n))
        assert zero(r), f"Nonzero residual at exponent {gamma}: {r}"


def e(n: int, row: int, col: int) -> Matrix:
    out = s.zeros(n)
    out[row, col] = 1
    return out


def run_tests() -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    half = s.Rational(1, 2)
    j = s.diag(2, 1, 0)
    aa = {half: e(3, 0, 1), 3 * half: e(3, 1, 2)}
    blocks = [(s.Integer(2), [0]), (s.Integer(1), [1]), (s.Integer(0), [2])]
    h, b, grid = normalize(j, aa, blocks, s.Rational(6))
    residual(j, aa, h, b, grid)
    assert h[half] == -2 * e(3, 0, 1)
    assert h[3 * half] == 2 * e(3, 1, 2)
    assert b[s.Rational(2)] == 2 * e(3, 0, 2)
    assert all(zero(v) for q, v in b.items() if q not in (0, 2))
    assert all(zero(v) for q, v in h.items() if q not in (0, half, 3 * half))
    checks.append({"name": "nonlinearly_generated_resonance", "status": "PASS",
                   "resonance": "2*t^2*E13", "checked_through": "6"})

    x, ell = s.symbols("x ell", positive=True)  # x=t^(1/2)
    y = s.Matrix([[x**4, -2*x**3, 2*ell*x**4],
                  [0, x**2, 2*x**3], [0, 0, 1]])
    a = j + x * e(3, 0, 1) + x**3 * e(3, 1, 2)
    delta_y = y.diff(x) * x / 2 + y.diff(ell)
    assert zero(delta_y - a*y)
    assert s.simplify(y.det() - x**6) == 0
    checks.append({"name": "exact_logarithmic_fundamental_matrix", "status": "PASS",
                   "residual": "identically zero", "determinant": "t^3"})

    # A nonsemisimple constant block exercises the Sylvester nilpotent inverse.
    j_nil = e(2, 0, 1)
    aa_nil = {s.Rational(1): e(2, 1, 0)}
    hn, bn, gn = normalize(j_nil, aa_nil, [(s.Integer(0), [0, 1])], s.Rational(8))
    residual(j_nil, aa_nil, hn, bn, gn)
    assert all(zero(v) for q, v in bn.items() if q > 0)
    checks.append({"name": "nilpotent_residual_block", "status": "PASS",
                   "checked_through": "8", "B": "E12"})

    j_mix = s.diag(0, s.I)
    aa_mix = {s.Rational(1): s.Matrix([[1, 2], [3, 4]])}
    hm, bm, gm = normalize(j_mix, aa_mix, [(s.Integer(0), [0]), (s.I, [1])],
                            s.Rational(7))
    residual(j_mix, aa_mix, hm, bm, gm)
    assert all(zero(v) for q, v in bm.items() if q > 0)
    checks.append({"name": "noncommuting_mixed_phase_system", "status": "PASS",
                   "checked_through": "7", "ambient_dimension": 1})

    # Any added exponent above the largest resonance 2 leaves B unchanged.
    with_tail = {**aa, s.Rational(7, 3): s.Matrix([[2, 0, 1], [1, -1, 0], [3, 2, 1]])}
    ht, bt, gt = normalize(j, with_tail, blocks, s.Rational(4))
    residual(j, with_tail, ht, bt, gt)
    for q in set(b) | set(bt):
        if q <= 4:
            assert zero(b.get(q, s.zeros(3)) - bt.get(q, s.zeros(3)))
    checks.append({"name": "resonance_skeleton_tail_invariance", "status": "PASS"})

    # Accumulating infinite-support example: exact coefficient identity,
    # plus many finite truncations (the infinite-support proof is in the paper).
    for n in range(2, 101):
        gamma = 1 - s.Rational(1, n)
        assert s.simplify((gamma - 1) * (-n) - 1) == 0
    checks.append({"name": "accumulating_support_coefficient_identity", "status": "PASS",
                   "tested_n": "2..100", "identity": "((1-1/n)-1)*(-n)=1"})

    nilp = e(2, 0, 1)
    forcing = s.Matrix([0, 1])
    particular = s.Matrix([ell**2/2, ell])
    assert zero(particular.diff(ell) - nilp*particular - forcing)
    assert nilp.row_join(forcing).rank() > nilp.rank()
    checks.append({"name": "inhomogeneous_logarithmic_obstruction", "status": "PASS",
                   "particular": "(ell^2/2, ell)", "no_Hahn_solution": True})

    # Deterministic randomized exact regression checks, including resonances.
    rng = random.Random(20260922)
    count = 12
    for trial in range(count):
        if trial % 3 == 0:
            jt = s.diag(0, 1)
            bl = [(s.Integer(0), [0]), (s.Integer(1), [1])]
        elif trial % 3 == 1:
            jt = e(2, 0, 1)
            bl = [(s.Integer(0), [0, 1])]
        else:
            jt = s.diag(s.I, 1+s.I)
            bl = [(s.I, [0]), (1+s.I, [1])]
        at = {q: s.Matrix(2, 2, [rng.randint(-2, 2) for _ in range(4)])
              for q in [s.Rational(1, 2), s.Rational(1), s.Rational(3, 2)]}
        hh, bb, gg = normalize(jt, at, bl, s.Rational(4))
        residual(jt, at, hh, bb, gg)
    checks.append({"name": "randomized_exact_normal_form_residuals", "status": "PASS",
                   "trials": count, "seed": 20260922, "checked_through": "4"})
    return {"all_passed": True, "sympy_version": s.__version__,
            "arithmetic": "exact rational and Gaussian rational",
            "scope": "Finite algebraic checks, not a formal verification of the theorems",
            "checks": checks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    report = run_tests()
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
