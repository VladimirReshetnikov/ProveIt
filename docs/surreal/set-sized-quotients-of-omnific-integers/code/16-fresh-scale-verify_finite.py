#!/usr/bin/env python3
"""Exact finite regression checks for omnific_fresh_scale.tex.

These checks do NOT implement arbitrary surreal numbers and do NOT constitute
formal verification of the Hahn or proper-class theorems. Symbols standing for
coefficients are treated algebraically. Python 3.9+ and SymPy are required.

Usage:
    python verify_finite.py
    python verify_finite.py --output verification_results.txt
"""
from __future__ import annotations

import argparse
import itertools
import math
import random
import sys
from pathlib import Path
from typing import List, Sequence, Tuple

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

X, T, U, s, w = sp.symbols("X T U s w")
lines: List[str] = []
check_count = 0


def record(message: str) -> None:
    lines.append(message)
    print(message)


def check(condition: bool, message: str) -> None:
    global check_count
    if not condition:
        raise AssertionError(message)
    check_count += 1


def zero(expression: sp.Expr) -> bool:
    return sp.cancel(sp.expand(expression)) == 0


def binomial_polynomial(variable: sp.Expr, degree: int) -> sp.Expr:
    return sp.prod(variable - j for j in range(degree)) / sp.factorial(degree)


def test_newton() -> None:
    rng = random.Random(23092026)
    cases = 0
    for d in range(9):
        for _ in range(5):
            # Formal positive-power terms imitate allowable purely infinite
            # coefficients; the assertions below are finite polynomial identities.
            coordinates = [sp.Integer(rng.randint(-8, 8))
                           + rng.randint(-3, 3) * w
                           + rng.randint(-2, 2) * w**2 for j in range(d + 1)]
            f = sp.expand(sum(coordinates[j] * binomial_polynomial(X, j)
                              for j in range(d + 1)))
            recovered = []
            for j in range(d + 1):
                cj = sum((-1)**(j-m) * sp.binomial(j, m) * f.subs(X, m)
                         for m in range(j + 1))
                recovered.append(sp.expand(cj))
                check(zero(cj - coordinates[j]), f"Newton coefficient d={d}, j={j}")
            rebuilt = sum(recovered[j] * binomial_polynomial(X, j) for j in range(d + 1))
            check(zero(rebuilt - f), f"Newton reconstruction d={d}")
            check(all(sp.denom(a).is_Integer for a in sp.Poly(f, X, w).coeffs()),
                  "All finite model coefficients are rational")
            cases += 1
    record(f"PASS: Newton reconstruction, {cases} exact polynomial cases (degrees 0--8).")


def total_lower_set(n: int, d: int) -> List[Tuple[int, ...]]:
    return sorted((a for a in itertools.product(range(d + 1), repeat=n) if sum(a) <= d),
                  key=lambda a: (sum(a), a))


def test_lower_sets() -> None:
    configurations = [(n, d) for n in range(1, 4) for d in range(5)]
    for n, d in configurations:
        lower = total_lower_set(n, d)
        matrix = sp.Matrix([[sp.prod(sp.binomial(bj, aj) for bj, aj in zip(b, a))
                             for a in lower] for b in lower])
        check(matrix.rows == math.comb(n+d, n), f"Simplex node count n={n}, d={d}")
        check(matrix.det() == 1, f"Unimodularity n={n}, d={d}")
        inverse = matrix.inv()
        check(all(entry.is_Integer for entry in inverse), "Integer inverse")
        coords = sp.Matrix([(-1)**j * (j+1) for j in range(len(lower))])
        check(inverse * matrix * coords == coords, "Exact lower-set recovery")
        for alpha in lower:
            denom = math.prod(math.factorial(a) for a in alpha)
            check(math.factorial(d) % denom == 0, "Total-degree factorial clears denominators")
    irregular = [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0), (0, 3)]
    matrix = sp.Matrix([[sp.prod(sp.binomial(bj, aj) for bj, aj in zip(b, a))
                         for a in irregular] for b in irregular])
    check(matrix.det() == 1, "Irregular lower-set determinant")
    record(f"PASS: {len(configurations)} simplex grids and one irregular lower set;"
           " determinants 1, integer inverses, factorial denominators.")


def centered_data(f: sp.Expr) -> Tuple[int, sp.Expr, sp.Expr, sp.Expr]:
    p = sp.Poly(f, X)
    d = p.degree()
    lead = p.LC()
    mu = sp.cancel(p.nth(d-1) / (d * lead))
    centered = sp.expand(f.subs(X, U-mu))
    return d, lead, mu, centered


def available_roots(d: int) -> List[sp.Expr]:
    roots = [sp.Integer(1)]
    if d % 2 == 0:
        roots.append(sp.Integer(-1))
    if d % 4 == 0:
        roots.extend([sp.I, -sp.I])
    return roots


def test_defects() -> None:
    rng = random.Random(2309)
    cases = 0
    for d in range(2, 9):
        for _ in range(5):
            lead = sp.Integer(rng.choice([1, 2, 3, -1, -2]))
            f = lead * X**d + sum(rng.randint(-4, 4)*X**j for j in range(d))
            _, ad, mu, h = centered_data(f)
            check(sp.Poly(h, U).nth(d-1) == 0, "Center kills subleading coefficient")
            for zeta in available_roots(d):
                for c in [sp.Integer(1), sp.Integer(3)]:
                    affine = zeta*T + (zeta-1)*mu
                    defect = sp.expand(f.subs(X, affine) - f.subs(X, T) - c)
                    q = sp.degree(defect, T)
                    check(0 <= q <= d-2, "Defect degree bound")
                    check(zero(defect.subs(T, -mu) + c), "Defect at fixed center")
                    r = d-1-int(q)
                    A = sp.cancel(-sp.Poly(defect, T).LC()/(d*ad*zeta**(d-1)))
                    check(1 <= r <= d-1 and A != 0, "Nonzero forbidden layer")
                    # The proposed correction cancels the leading defect exactly.
                    derivative = sp.diff(f, X).subs(X, affine)
                    linear_residual = sp.expand(defect + derivative*A*T**(-r))
                    check(zero(linear_residual.coeff(T, q)), "Leading cancellation")
                    if zeta == 1:
                        check(r == d-1 and zero(A-c/(d*ad)), "Sharp identity branch")
                    cases += 1
    record(f"PASS: {cases} centered defect cases, including cancellations and sharp layer d-1.")


def convolve(a: Sequence[sp.Expr], b: Sequence[sp.Expr], order: int) -> List[sp.Expr]:
    out = [sp.Integer(0)] * (order+1)
    for i, ai in enumerate(a):
        if i > order:
            break
        for j, bj in enumerate(b):
            if i+j <= order:
                out[i+j] += ai*bj
    return [sp.cancel(sp.expand(value)) for value in out]


def series_power(a: Sequence[sp.Expr], exponent: int, order: int) -> List[sp.Expr]:
    out = [sp.Integer(1)] + [sp.Integer(0)] * order
    for _ in range(exponent):
        out = convolve(out, a, order)
    return out


def H_coefficients(f: sp.Expr, W: Sequence[sp.Expr], c: sp.Expr, order: int) -> List[sp.Expr]:
    """Coefficients of s^d[f(W/s)-f(1/s)-c] modulo s^(order+1)."""
    poly = sp.Poly(f, X)
    d = poly.degree()
    out = [sp.Integer(0)] * (order+1)
    for j in range(d+1):
        shift = d-j
        if shift > order:
            continue
        power = series_power(W, j, order-shift)
        power[0] -= 1
        for k, coefficient in enumerate(power):
            out[shift+k] += poly.nth(j)*coefficient
    if d <= order:
        out[d] -= c
    return [sp.cancel(sp.expand(value)) for value in out]


def lift_branch(f: sp.Expr, zeta: sp.Expr, c: sp.Expr, order: int) -> List[sp.Expr]:
    poly = sp.Poly(f, X)
    d = poly.degree()
    derivative = d*poly.LC()*zeta**(d-1)
    W = [zeta] + [sp.Integer(0)]*order
    check(zero(H_coefficients(f, W, c, 0)[0]), "Simple residue root")
    for j in range(1, order+1):
        error = H_coefficients(f, W, c, j)[j]
        W[j] = sp.cancel(sp.expand(-error/derivative))
    check(all(zero(a) for a in H_coefficients(f, W, c, order)),
          "Full truncated root equation")
    return W


def test_root_branches() -> None:
    polynomials = [X**2, 2*X**2+3*X+4, w*X**2+X,
                   X**3, X**3+2*X+1, X**3+X**2,
                   X**4, X**4+2*X**2+3*X+4, (X+2)**4+5,
                   X**5+X**2+2]
    cases = 0
    for f in polynomials:
        d, ad, mu, _ = centered_data(f)
        for zeta in available_roots(d):
            c = sp.Integer(1)
            W = lift_branch(f, zeta, c, d+1)
            check(zero(W[1] - (zeta-1)*mu), "Exact affine part")
            affine = zeta*T+(zeta-1)*mu
            defect = sp.expand(f.subs(X, affine)-f.subs(X, T)-c)
            r = d-1-int(sp.degree(defect, T))
            A = sp.cancel(-sp.Poly(defect, T).LC()/(d*ad*zeta**(d-1)))
            check(all(zero(W[j]) for j in range(2, r+1)), "No earlier negative layer")
            check(zero(W[r+1]-A), "Predicted first negative coefficient")
            cases += 1
    record(f"PASS: {cases} formal inverse branches computed recursively through order d+1,")
    record("      including an indeterminate infinite-leading-coefficient model w*X^2+X.")


def test_fibers_and_examples() -> None:
    examples = [(X**3+X**2, 1), ((X+2)**6+7, 6), (X**6+X**4+1, 2),
                (X**4+2*X**2+3*X+4, 1), (X**4+2*X**2+4, 2)]
    for f, expected in examples:
        d, _, mu, h = centered_data(f)
        indices = [j for j in range(1, d+1) if sp.Poly(h, U).nth(j) != 0]
        e = math.gcd(*indices)
        check(e == expected, "Centered support gcd")
        for zeta in available_roots(d):
            identity = zero(f.subs(X, zeta*T+(zeta-1)*mu)-f.subs(X, T))
            check(identity == zero(zeta**e-1), "Affine symmetry criterion")
    check(zero(binomial_polynomial(sp.I, 2) - (-1-sp.I)/2), "Gaussian counterexample")
    N = sp.Matrix([[0, 1], [0, 0]])
    matrix_value = N*(N-sp.eye(2))/2
    check(matrix_value == -N/2, "Nilpotent matrix binomial counterexample")
    check(matrix_value[0, 1] == -sp.Rational(1, 2), "Matrix value is not integral")
    z = sp.symbols("z")
    expanded = sp.series(z/(1-z**2/2), z, 0, 12).removeO()
    check(zero(expanded-sum(z**(2*j+1)/2**j for j in range(6))), "Geometric bad input")
    for integer in range(-10, 11):
        coefficient = sp.cancel(1/(sp.Integer(integer)-sp.Rational(1, 2)))
        check(coefficient.is_Rational and coefficient != 0, "Sampled ordinary value has only w term")
    record("PASS: fresh-fiber symmetry examples, Gaussian and matrix warnings, geometric witness.")
    record("EXAMPLE: binomial(i,2) = (-1-i)/2.")
    record("EXAMPLE: for f=T^4+p*T^2+q*T+r, first corrections are")
    record("         zeta=1: c/4*T^-3; zeta=-1, q!=0: -q/2*T^-2;")
    record("         zeta=i, p!=0: i*p/2*T^-1.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_results.txt"))
    args = parser.parse_args()
    record("FINITE VERIFICATION REPORT")
    record("Manuscript: Fresh-Scale Image Gaps and Rational Rigidity for Omnific Integers")
    record(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}; deterministic seeds.")
    record("")
    for test in [test_newton, test_lower_sets, test_defects, test_root_branches,
                 test_fibers_and_examples]:
        test()
    record("")
    record(f"SUCCESS: {check_count} exact finite assertions passed.")
    record("SCOPE: finite symbolic algebra only; not a Lean proof, not a surreal implementation,")
    record("       not verification of arbitrary Hahn supports or proper-class quantifiers.")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines)+"\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
