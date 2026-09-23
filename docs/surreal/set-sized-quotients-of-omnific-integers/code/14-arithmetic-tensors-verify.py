#!/usr/bin/env python3
"""Exact finite checks for Arithmetic Tensors in the Omnific Integers.

Requires Python 3.9+ and SymPy. These are regression checks for finite
consequences, not a formal verification of the manuscript's theorems.
Run: python verify.py --output verification.json
"""
from __future__ import annotations
import argparse
import json
import platform
import random
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple, List

try:
    import sympy as sp
    from sympy.matrices.normalforms import hermite_normal_form
except ImportError as exc:
    raise SystemExit("SymPy is required. Run: python -m pip install -r requirements.txt") from exc

# Q(sqrt(2)), represented as a + b sqrt(2). All calculations are exact.
Q2 = Tuple[Fraction, Fraction]
ZERO: Q2 = (Fraction(0), Fraction(0))
ONE: Q2 = (Fraction(1), Fraction(0))

def qadd(a: Q2, b: Q2) -> Q2:
    return a[0] + b[0], a[1] + b[1]

def qmul(a: Q2, b: Q2) -> Q2:
    return a[0]*b[0] + 2*a[1]*b[1], a[0]*b[1] + a[1]*b[0]

def qscale(d: int, a: Q2) -> Q2:
    return d*a[0], d*a[1]

# Finite strictly positive rational exponents; a member of P over Q(sqrt(2)).
Poly = Dict[Fraction, Q2]

def padd(a: Poly, b: Poly) -> Poly:
    out = dict(a)
    for e, c in b.items():
        out[e] = qadd(out.get(e, ZERO), c)
        if out[e] == ZERO:
            del out[e]
    return out

def pscale(a: Poly, c: Q2) -> Poly:
    return {e: qmul(v, c) for e, v in a.items() if qmul(v, c) != ZERO}

def pmul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for e, c in a.items():
        for f, d in b.items():
            out = padd(out, {e+f: qmul(c, d)})
    return out

# M=Z+sqrt(2)Z. Constant tensor basis is 1x1,1xa,ax1,axa.
Tensor = Tuple[int, int, int, int]
Elt = Tuple[Poly, Tensor]
Scalar = Tuple[int, Poly]
LatticeElt = Tuple[Tuple[int, int], Poly]

def mu(t: Tensor) -> Q2:
    return Fraction(t[0] + 2*t[3]), Fraction(t[1] + t[2])

def smul(a: Scalar, b: Scalar) -> Scalar:
    d, h = a
    e, g = b
    return d*e, padd(padd(pscale(g, (Fraction(d), Fraction(0))),
                           pscale(h, (Fraction(e), Fraction(0)))), pmul(h, g))

def action(a: Scalar, x: Elt) -> Elt:
    d, h = a
    u, t = x
    first = padd(padd(pscale(u, (Fraction(d), Fraction(0))), pmul(h, u)),
                 pscale(h, mu(t)))
    return first, tuple(d*v for v in t)

def lattice_action(a: Scalar, x: LatticeElt) -> LatticeElt:
    d, h = a
    m, u = x
    mq = (Fraction(m[0]), Fraction(m[1]))
    first = (d*m[0], d*m[1])
    return first, padd(padd(pscale(u, (Fraction(d), Fraction(0))), pmul(h, u)),
                       pscale(h, mq))

def beta(x: LatticeElt, y: LatticeElt) -> Elt:
    m, u = x
    n, v = y
    mq, nq = (Fraction(m[0]), Fraction(m[1])), (Fraction(n[0]), Fraction(n[1]))
    pure = (m[0]*n[0], m[0]*n[1], m[1]*n[0], m[1]*n[1])
    return padd(padd(pscale(v, mq), pscale(u, nq)), pmul(u, v)), pure

def randpoly(rng: random.Random) -> Poly:
    out: Poly = {}
    for _ in range(rng.randint(0, 4)):
        e = Fraction(rng.randint(1, 12), rng.randint(1, 6))
        c = (Fraction(rng.randint(-3, 3), rng.randint(1, 3)),
             Fraction(rng.randint(-3, 3), rng.randint(1, 3)))
        out = padd(out, {e: c})
    return out

def power_column(d: int, j: int) -> sp.Matrix:
    """Coordinates of alpha^j in Q[alpha]/(alpha^d-2)."""
    col = [0] * d
    col[j % d] = 2 ** (j // d)
    return sp.Matrix(col)

def main(output: Path) -> dict:
    checks = 0
    def check(condition: bool, description: str) -> None:
        nonlocal checks
        if not condition:
            raise AssertionError(description)
        checks += 1

    degree_cases: List[dict] = []
    for d in range(2, 11):
        for n in range(1, 13):
            matrix = sp.Matrix.hstack(*(power_column(d, j) for j in range(n+1)))
            rank = int(matrix.rank())
            check(rank == min(n+1, d), f"product rank d={d},n={n}")
            check(n+1-rank == max(0, n-d+1), f"symmetric nullity d={d},n={n}")
            if n < d:
                check(len(matrix.nullspace()) == 0, f"no early equation d={d},n={n}")
            else:
                relations = []
                for j in range(n-d+1):
                    col = [0]*(n+1)
                    col[j] = -2
                    col[j+d] = 1
                    relations.append(sp.Matrix(col))
                relmat = sp.Matrix.hstack(*relations)
                check(matrix*relmat == sp.zeros(d, n-d+1), "homogenized relation")
                check(relmat.rank() == n+1-rank, "all degree-n relations accounted for")
            degree_cases.append({"d": d, "n": n, "product_rank": rank,
                                 "symmetric_kernel_rank": n+1-rank})

    tensor_cases = []
    for d in range(2, 8):
        for n in range(1, 8):
            cols = [power_column(d, bin(word).count('1')) for word in range(2**n)]
            matrix = sp.Matrix.hstack(*cols)
            rank = int(matrix.rank())
            nullity = 2**n - rank
            check(rank == min(n+1, d), "ordered tensor product rank")
            check(nullity == 2**n-min(n+1,d), "ordered tensor kernel rank")
            tensor_cases.append({"d":d, "n":n, "kernel_rank":nullity})

    X, Y, Z, alpha = sp.symbols('X Y Z alpha')
    for d in range(2, 11):
        eq = Y**d-2*X**d
        check(sp.rem(eq.subs(Y, X*Z), Z**d-2, Z) == 0, "Rees equation evaluation")
    # A formal indeterminate models transcendence exactly in each finite degree.
    for n in range(1, 21):
        powers = [sp.Poly(alpha**j, alpha) for j in range(n+1)]
        coeff_matrix = sp.Matrix([[p.nth(j) for p in powers] for j in range(n+1)])
        check(coeff_matrix.det() == 1, "formal transcendental independence")

    torsion_basis = [(0,1,-1,0), (-2,0,0,1)]
    check(sp.Matrix.hstack(*(sp.Matrix(t) for t in torsion_basis)).rank() == 2,
          "quadratic torsion generators independent")
    for t in torsion_basis:
        check(mu(t) == ZERO, "quadratic tensor product zero")
        check(t != (0,0,0,0), "quadratic tensor itself nonzero")

    # P=(2,sqrt(10)), relative to O's basis (1,sqrt(10)).
    product_generators = sp.Matrix([[4,0,10],[0,2,0]])
    hnf = hermite_normal_form(product_generators)
    check(hnf == 2*sp.eye(2), "P squared is 2O")
    check(3*4-10 == 2, "explicit integer Bezout combination")
    square_residues = {a*a % 5 for a in range(5)}
    check(not ({2,3} & square_residues), "norm plus/minus 2 obstruction")
    a, b = sp.symbols('a b')
    check(sp.Matrix([[a,10*b],[b,a]]).det() == a*a-10*b*b, "quadratic norm determinant")

    rng = random.Random(20260923)
    random_cases = 120
    for case in range(random_cases):
        scalar_a = (rng.randint(-3,3), randpoly(rng))
        scalar_b = (rng.randint(-3,3), randpoly(rng))
        elt = (randpoly(rng), tuple(rng.randint(-3,3) for _ in range(4)))
        check(action(scalar_a, action(scalar_b, elt)) == action(smul(scalar_a, scalar_b), elt),
              f"action associativity case {case}")
        check(action((1,{}), elt) == elt, "unit action")
        left = ((rng.randint(-3,3), rng.randint(-3,3)), randpoly(rng))
        right = ((rng.randint(-3,3), rng.randint(-3,3)), randpoly(rng))
        check(beta(lattice_action(scalar_a,left), right) == beta(left,lattice_action(scalar_a,right)),
              "bilinear balancing")
        check(beta(lattice_action(scalar_a,left), right) == action(scalar_a,beta(left,right)),
              "normal form linearity")
        for t in torsion_basis:
            check(action((0,scalar_a[1]), ({},t)) == ({},(0,0,0,0)),
                  "purely infinite scalar kills torsion")
        # Finite common factor strictly below every input support exponent.
        family = [left[1], right[1], scalar_a[1], scalar_b[1]]
        support = [e for p in family for e in p]
        if support:
            delta = min(support)/2
            for poly in family:
                shifted = {e-delta:c for e,c in poly.items()}
                check(all(e>0 for e in shifted), "strictly positive quotient support")
                check(pmul({delta:ONE}, shifted) == poly, "common monomial factor")

    report = {
        "status":"PASS", "assertions_passed":checks,
        "python":platform.python_version(), "sympy":sp.__version__,
        "seed":20260923,
        "symmetric_degree_cases":degree_cases,
        "ordered_tensor_cases":tensor_cases,
        "finite_support_action_cases":random_cases,
        "formal_transcendental_degrees_checked":list(range(1,21)),
        "sqrt10_product_hnf":[[int(v) for v in row] for row in hnf.tolist()],
        "square_residues_mod_5":sorted(square_residues),
        "limitations":["Not a formal proof of the manuscript",
                       "No exhaustive test of surreal supports or class universal properties",
                       "No verification of historical priority"]
    }
    output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(f"PASS: {checks} exact assertions; report: {output}")
    return report

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('verification.json'))
    args = parser.parse_args()
    main(args.output)
