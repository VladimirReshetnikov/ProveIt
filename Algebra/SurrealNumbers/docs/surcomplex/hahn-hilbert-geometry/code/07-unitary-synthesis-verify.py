#!/usr/bin/env python3
"""Exact finite diagnostics for article.tex.

Requires SymPy 1.14.0. Tests truncated rational matrix series only; it does
not prove infinite-dimensional boundedness, Hahn support assertions, or
novelty. Run: python verify.py [--output verification_results.json]
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

import sympy as sp

Matrix = sp.MatrixBase
Series = list[Matrix]
RESULTS: list[dict[str, object]] = []


def zero(d: int, order: int) -> Series:
    return [sp.zeros(d) for _ in range(order + 1)]


def const(a: Matrix, order: int) -> Series:
    out = zero(a.rows, order)
    out[0] = sp.Matrix(a)
    return out


def add(a: Series, b: Series) -> Series:
    if len(a) != len(b):
        raise ValueError("Truncation orders do not match")
    return [x + y for x, y in zip(a, b)]


def neg(a: Series) -> Series:
    return [-x for x in a]


def sub(a: Series, b: Series) -> Series:
    return add(a, neg(b))


def scale(a: Series, c: sp.Expr) -> Series:
    return [c * x for x in a]


def mul(a: Series, b: Series) -> Series:
    if len(a) != len(b):
        raise ValueError("Truncation orders do not match")
    out = zero(a[0].rows, len(a) - 1)
    for k in range(len(a)):
        for j in range(k + 1):
            out[k] += a[j] * b[k - j]
    return out


def adj(a: Series) -> Series:
    return [x.conjugate().T for x in a]


def power_series_at_positive(r: Series, coeff: Sequence[sp.Expr]) -> Series:
    if r[0] != sp.zeros(r[0].rows):
        raise ValueError("Formal substitution requires zero constant term")
    n = len(r) - 1
    p = const(sp.eye(r[0].rows), n)
    out = zero(r[0].rows, n)
    for c in coeff[: n + 1]:
        out = add(out, scale(p, c))
        p = mul(p, r)
    return out


def inverse_near_identity(a: Series) -> Series:
    n = len(a) - 1
    ident = const(sp.eye(a[0].rows), n)
    return power_series_at_positive(sub(a, ident), [sp.Integer((-1) ** j) for j in range(n + 1)])


def inverse_sqrt_near_identity(a: Series) -> Series:
    n = len(a) - 1
    ident = const(sp.eye(a[0].rows), n)
    return power_series_at_positive(
        sub(a, ident), [sp.binomial(sp.Rational(-1, 2), j) for j in range(n + 1)]
    )


def exp_monomial(a: Matrix, shift: int, order: int) -> Series:
    if shift < 1:
        raise ValueError("Shift must be positive")
    out = zero(a.rows, order)
    p = sp.eye(a.rows)
    for k in range(order // shift + 1):
        out[k * shift] = p / sp.factorial(k)
        p = p * a
    return out


def check_series(name: str, a: Series, b: Series) -> None:
    if len(a) != len(b):
        raise AssertionError(f"{name}: mismatched lengths")
    for degree, (x, y) in enumerate(zip(a, b)):
        if x != y and any(sp.simplify(z) != 0 for z in x - y):
            raise AssertionError(f"{name}: failed at degree {degree}")
    RESULTS.append({"test": name, "status": "passed", "degree": len(a) - 1, "matrix_size": a[0].rows})


def check_matrix(name: str, a: Matrix, b: Matrix) -> None:
    if a != b and any(sp.simplify(z) != 0 for z in a - b):
        raise AssertionError(name)
    RESULTS.append({"test": name, "status": "passed", "shape": list(a.shape)})


def diag_compress(a: Series, es: list[Matrix]) -> Series:
    out = zero(a[0].rows, len(a) - 1)
    for k, coefficient in enumerate(a):
        for e in es:
            out[k] += e * coefficient * e
    return out


def coordinate_projection(d: int, indices: Sequence[int]) -> Matrix:
    e = sp.zeros(d)
    for j in indices:
        e[j, j] = 1
    return e


def test_construction(d: int, blocks: list[list[int]], order: int, tag: str) -> None:
    ident = const(sp.eye(d), order)
    a = sp.zeros(d)
    b = sp.zeros(d)
    for j in range(d - 1):
        a[j, j + 1] = sp.Rational(j + 1, j + 2)
        a[j + 1, j] = -a[j, j + 1]
    for j in range(d - 2):
        b[j, j + 2] = sp.Rational(2 * j + 1, j + 3)
        b[j + 2, j] = -b[j, j + 2]
    original = mul(exp_monomial(a, 1, order), exp_monomial(b, 2, order))
    es = [coordinate_projection(d, block) for block in blocks]
    e = sum(es, sp.zeros(d))
    f = sp.eye(d) - e
    ps = [mul(mul(original, const(ei, order)), adj(original)) for ei in es]
    c = zero(d, order)
    for pi, ei in zip(ps, es):
        c = add(c, mul(pi, const(ei, order)))
    g = add(mul(adj(c), c), const(f, order))
    ginv = inverse_near_identity(g)
    q = mul(mul(c, ginv), adj(c))
    t = add(c, mul(sub(ident, q), const(f, order)))
    w = mul(t, inverse_sqrt_near_identity(mul(adj(t), t)))

    def cs(label: str, x: Series, y: Series) -> None:
        check_series(f"{tag}/{label}", x, y)

    cs("original-left-unitary", mul(adj(original), original), ident)
    cs("original-right-unitary", mul(original, adj(original)), ident)
    cs("G-inverse", mul(g, ginv), ident)
    cs("Q-projection", mul(q, q), q)
    cs("Q-selfadjoint", adj(q), q)
    cs("Q-C", mul(q, c), c)
    cs("Q-T", mul(q, t), mul(t, const(e, order)))
    cs("constructed-left-unitary", mul(adj(w), w), ident)
    cs("constructed-right-unitary", mul(w, adj(w)), ident)
    cs("Q-is-transported-E", q, mul(mul(w, const(e, order)), adj(w)))
    cs("canonical-necessity-formula", c, mul(w, diag_compress(adj(w), es)))
    for j, (pi, ei) in enumerate(zip(ps, es)):
        ce = const(ei, order)
        cs(f"atom-{j}-projection", mul(pi, pi), pi)
        cs(f"atom-{j}-selfadjoint", adj(pi), pi)
        cs(f"atom-{j}-intertwining", mul(pi, t), mul(t, ce))
        cs(f"atom-{j}-straightening", mul(mul(w, ce), adj(w)), pi)
        cs(f"atom-{j}-under-Q", mul(q, pi), pi)
        for k in range(j):
            cs(f"atoms-{j}-{k}-orthogonal", mul(pi, ps[k]), zero(d, order))
    if e == sp.eye(d):
        polar = mul(c, inverse_sqrt_near_identity(mul(adj(c), c)))
        cs("complete-polar-formula", w, polar)
        check_matrix(f"{tag}/first-coefficient", w[1], c[1])
        check_matrix(
            f"{tag}/second-coefficient", w[2],
            (c[2] - c[2].T) / 2 - c[1].T * c[1] / 2,
        )
    # Independently rebuild all shorter jets to check finite-jet consistency
    # of this canonical construction, not just of the chosen original U.
    for n in range(order):
        cn = c[: n + 1]
        fn = const(f, n)
        gn = add(mul(adj(cn), cn), fn)
        qn = mul(mul(cn, inverse_near_identity(gn)), adj(cn))
        tn = add(cn, mul(sub(const(sp.eye(d), n), qn), fn))
        wn = mul(tn, inverse_sqrt_near_identity(mul(adj(tn), tn)))
        check_series(f"{tag}/jet-{n}", wn, w[: n + 1])


def test_flat_blocks() -> None:
    # Small square block dimensions test the exact identities. The theorem's
    # dimension d_m = 4^(m^2) and its infinite norm growth are proved in text.
    for m, d in [(1, 1), (2, 4), (3, 9)]:
        root = sp.sqrt(d)
        u = sp.Matrix([1 / root] * d + [0] * d)
        v = sp.Matrix([0] * d + [1 / root] * d)
        a = m * (v * u.T - u * v.T)
        active = u * u.T + v * v.T
        el = coordinate_projection(2 * d, list(range(d)))
        comm = a * el - el * a
        tag = f"flat-block-m{m}-d{d}"
        check_matrix(f"{tag}/skew", a.T, -a)
        check_matrix(f"{tag}/active-square", a.T * a, m * m * active)
        check_matrix(f"{tag}/half-commutator-square", comm.T * comm, m * m * active)
        first_c = sp.zeros(2 * d)
        for j in range(2 * d):
            ej = coordinate_projection(2 * d, [j])
            first_c += (a * ej - ej * a) * ej
        check_matrix(f"{tag}/first-synthesis", first_c, a)
        # Both a left and right coordinate, at several powers.
        for j in [0, d]:
            vec = sp.eye(2 * d)[:, j]
            for k in range(1, 6):
                vec = a * vec
                check_matrix(
                    f"{tag}/column-{j}-power-{k}", vec.T * vec,
                    sp.Matrix([[sp.Rational(m ** (2 * k), d)]]),
                )


def test_support_block(order: int = 10) -> None:
    j = sp.Matrix([[0, -1], [1, 0]])
    ident = const(sp.eye(2), order)
    q2 = zero(2, order)
    q2[2] = sp.eye(2)
    one_plus_qj = const(sp.eye(2), order)
    one_plus_qj[1] = j
    r = mul(one_plus_qj, inverse_sqrt_near_identity(add(ident, q2)))
    es = [coordinate_projection(2, [i]) for i in range(2)]
    ps = [mul(mul(r, const(e, order)), adj(r)) for e in es]
    c = add(mul(ps[0], const(es[0], order)), mul(ps[1], const(es[1], order)))
    expected = mul(one_plus_qj, inverse_near_identity(add(ident, q2)))
    check_series("support-block/unitary", mul(adj(r), r), ident)
    check_series("support-block/canonical-rational-expression", c, expected)
    check_series("support-block/projection-sum", add(ps[0], ps[1]), ident)
    for k in range(order + 1):
        target = (-1) ** (k // 2) * (sp.eye(2) if k % 2 == 0 else j)
        check_matrix(f"support-block/coefficient-{k}", c[k], target)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    test_construction(3, [[0], [1], [2]], 6, "complete-rank-one-d3")
    test_construction(4, [[0, 1], [2]], 6, "incomplete-blocks-d4")
    test_construction(5, [[0, 1], [2, 3], [4]], 5, "complete-blocks-d5")
    test_flat_blocks()
    test_support_block()
    report = {
        "status": "all exact finite checks passed",
        "sympy_version": sp.__version__,
        "assertion_groups": len(RESULTS),
        "arithmetic": "exact rational matrix coefficients; no floating point",
        "scope": "finite matrix power-series identities only",
        "not_verified": [
            "arbitrary ordered-group Hahn support lemma",
            "infinite-dimensional bounded extension and unboundedness",
            "proper-class operator representation",
            "independent proof review or priority",
            "Lean formalization",
        ],
        "tests": RESULTS,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Passed {len(RESULTS)} exact assertion groups; results: {args.output}")


if __name__ == "__main__":
    main()
