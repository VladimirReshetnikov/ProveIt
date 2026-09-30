#!/usr/bin/env python3
"""Exact finite checks for Algebraic Convergence Loci for Nonlinear Hahn Systems.

Requires Python 3.10+ and SymPy. This is NOT a proof assistant and does not
certify infinite-support well-ordering or convergence. All checks use exact
rational and symbolic arithmetic. Run from any directory:
    python verification/verify.py
"""
from __future__ import annotations
import json
import platform
import random
from collections import deque
from pathlib import Path
from typing import Iterable
import sympy as s

Q = s.Rational
CHECKS = 0
CASES: list[dict] = []

def check(actual, expected=0, *, label: str) -> None:
    global CHECKS
    if isinstance(actual, s.MatrixBase):
        expected = expected if isinstance(expected, s.MatrixBase) else s.zeros(*actual.shape)
        if actual.shape != expected.shape:
            raise AssertionError(f"{label}: shape mismatch")
        for x in actual - expected:
            if s.expand(x) != 0:
                raise AssertionError(f"{label}: {s.expand(x)}")
            CHECKS += 1
    else:
        if s.expand(actual - expected) != 0:
            raise AssertionError(f"{label}: {actual} != {expected}")
        CHECKS += 1


def semigroup(generators: Iterable, cutoff) -> list:
    """Enumerate a FINITELY generated positive rational monoid below cutoff."""
    gens = sorted(set(map(Q, generators)))
    cutoff = Q(cutoff)
    if not gens or any(g <= 0 for g in gens):
        raise ValueError("Positive rational generators are required.")
    seen = {Q(0)}
    queue = deque([Q(0)])
    while queue:
        x = queue.popleft()
        for g in gens:
            z = x + g
            if z <= cutoff and z not in seen:
                seen.add(z)
                queue.append(z)
    return sorted(seen)


def mul(a: dict, b: dict, cutoff) -> dict:
    out = {}
    for i, ai in a.items():
        for j, bj in b.items():
            if i + j <= cutoff:
                out[i+j] = out.get(i+j, 0) + ai*bj
    return {k: s.expand(v) for k, v in out.items() if s.expand(v) != 0}


def rhs_coefficient(terms: list, y: dict, gamma, dim: int):
    """terms are (x-exponent, multiindex in y, vector coefficient)."""
    out = s.zeros(dim, 1)
    coords = [{g: v[i] for g, v in y.items() if v[i] != 0}
              for i in range(dim)]
    for alpha, powers, coeff in terms:
        alpha = Q(alpha)
        if alpha > gamma:
            continue
        if len(powers) != dim or any(k < 0 for k in powers):
            raise ValueError("Invalid multiindex.")
        if alpha == 0 and sum(powers) <= 1:
            raise ValueError("F(0,0)=0 and F_y(0,0)=0 are required.")
        h = {Q(0): s.Integer(1)}
        for i, power in enumerate(powers):
            for _ in range(power):
                h = mul(h, coords[i], gamma-alpha)
        out += s.Matrix(coeff) * h.get(gamma-alpha, 0)
    return out.applyfunc(s.expand)


def split_inverse(T):
    """Return R, Q=I-TR and a kernel basis, using rational pivot splittings."""
    n = T.rows
    if T.cols != n:
        raise ValueError("Square matrix required.")
    pivots = T.rref()[1]
    rank = len(pivots)
    K = T.nullspace()
    if rank == n:
        return T.inv(), s.zeros(n), []
    R = s.zeros(n)
    if rank:
        C = T[:, list(pivots)]
        rows = C.T.rref()[1]
        B = C[list(rows), :]
        U = s.eye(n)[:, list(pivots)]
        E = s.eye(n)[list(rows), :]
        R = U*B.inv()*E
    P = s.eye(n) - T*R
    check(T*R*T, T, label="generalized inverse TRT=T")
    check(P*P, P, label="cokernel projection")
    for k in K:
        check(T*k, label="kernel basis")
    return R, P, K


def solve_finite(A, terms: list, generators: list, cutoff, name: str):
    A = s.Matrix(A)
    dim = A.rows
    exponents = semigroup(generators, cutoff)
    y, obstruction, params = {}, {}, {}
    for gamma in exponents:
        if gamma == 0:
            continue
        f = rhs_coefficient(terms, y, gamma, dim)
        T = gamma*s.eye(dim) - A
        R, P, kernel = split_inverse(T)
        v = R*f
        if kernel:
            cs = s.symbols(f"c_{str(gamma).replace('/', '_')}_0:{len(kernel)}")
            params[gamma] = cs
            for c, k in zip(cs, kernel):
                v += c*k
            obstruction[gamma] = (P*f).applyfunc(s.expand)
        y[gamma] = v.applyfunc(s.expand)
    for gamma in exponents:
        if gamma == 0:
            continue
        residual = (gamma*s.eye(dim)-A)*y[gamma] - rhs_coefficient(terms, y, gamma, dim)
        check(residual, -obstruction.get(gamma, s.zeros(dim,1)),
              label=f"{name}: residual at {gamma}")
    CASES.append({"name": name, "exponents_checked": len(exponents)-1,
                  "resonances": list(map(str, params)),
                  "obstructions": {str(k): list(map(str,v)) for k,v in obstruction.items()}})
    return y, obstruction, params


def main() -> None:
    global CHECKS
    CHECKS = 0
    CASES.clear()
    a, b = s.symbols('a b')
    sharp = []
    for n in range(2, 8):
        terms = [(1,(0,),[a]), (0,(2,),[b])]
        y, obs, _ = solve_finite([[n]], terms, [1], n, f"sharp degree n={n}")
        expected = a**n*b**(n-1)/s.factorial(n-1)**2
        check(obs[Q(n)][0], expected, label=f"sharp obstruction n={n}")
        sharp.append({"n": n, "coefficient": str(1/s.factorial(n-1)**2),
                      "total_degree": 2*n-1})

    # An independent rational recurrence extends the exact sharpness test.
    for n in range(2, 26):
        v = {1: -Q(1,n-1)}
        for j in range(2,n):
            v[j] = sum(v[i]*v[j-i] for i in range(1,j))/Q(j-n)
        k = sum(v[i]*v[n-i] for i in range(1,n))
        check(k, 1/s.factorial(n-1)**2, label=f"Riccati coefficient n={n}")

    # Hidden nonlinear small divisors: exact finite restrictions of the
    # infinite support {2-1/n:n>=3}. Finite restrictions are not convergence tests.
    tails = list(range(3,9))
    ds = {n:s.Symbol(f'd{n}') for n in tails}
    E = [Q(1)] + [2-Q(1,n) for n in tails]
    terms = [(1,(0,),[a]), (0,(2,),[b]), (0,(3,),[2*b*b])]
    terms += [(2-Q(1,n),(0,),[ds[n]]) for n in tails]
    y, obs, par = solve_finite([[3]],terms,E,3,"nonlinear generated small divisors")
    check(obs[Q(3)], label="exact cubic cancellation")
    check(y[Q(1)][0],-a/2,label="coefficient at 1")
    check(y[Q(2)][0],-a*a*b/4,label="coefficient at 2")
    for n in tails:
        check(y[2-Q(1,n)][0],-Q(n,n+1)*ds[n],label=f"input exponent n={n}")
        check(y[3-Q(1,n)][0],-Q(n*n,n+1)*a*b*ds[n],label=f"generated exponent n={n}")
    ancestors = [x for x in semigroup(E,3) if Q(3)-x in semigroup(E,3)]
    if ancestors != list(map(Q,[0,1,2,3])):
        raise AssertionError("The critical ancestor set differs from {0,1,2,3}.")

    # Arbitrary-variety construction, illustrated by a circle and xy=0.
    ns = [2,3,4]
    E = [Q(1)] + [1-Q(1,n) for n in ns]
    terms = []
    for n in ns:
        e, w = 1-Q(1,n), Q(1,n*n)
        terms.extend([(e,(2,0,0,0),[0,0,w,0]),
                      (e,(0,2,0,0),[0,0,w,0]),
                      (e+2,(0,0,0,0),[0,0,-w,0]),
                      (e,(1,1,0,0),[0,0,0,w])])
    y, obs, par = solve_finite(s.diag(1,1,3,3),terms,E,3,"algebraic-locus universality")
    c1,c2 = par[Q(1)]
    for o in obs.values():
        check(o,label="universality: no exact resonance obstruction")
    for n in ns:
        check(y[3-Q(1,n)][2],-(c1*c1+c2*c2-1)/n,label=f"circle obstruction n={n}")
        check(y[3-Q(1,n)][3],-c1*c2/n,label=f"product obstruction n={n}")
    for c1v,c2v in [(1,0),(-1,0),(0,1),(0,-1)]:
        for n in ns:
            check(y[3-Q(1,n)].subs({c1:c1v,c2:c2v}),label="selected analytic parameters")

    # A nonsemisimple residue: the cokernel is not the kernel.
    y, obs, par = solve_finite([[1,1],[0,1]],[(1,(0,0),[b,a])],[1],3,"Jordan cokernel")
    check(obs[Q(1)],s.Matrix([0,a]),label="Jordan obstruction")
    c = par[Q(1)][0]
    check(y[Q(1)],s.Matrix([c,-b]),label="Jordan particular plus kernel")

    rng = random.Random(20260929)
    for case in range(12):
        A = s.diag(1,2) if case < 8 else s.Matrix([[1,1],[0,1]])
        coeff = lambda: [s.Integer(rng.randrange(-2,3)) for _ in range(2)]
        terms = [(1,(0,0),coeff()),(2,(0,0),coeff()),
                 (1,(1,0),coeff()),(1,(0,1),coeff()),
                 (0,(2,0),coeff()),(0,(1,1),coeff())]
        solve_finite(A,terms,[1],4,f"seeded exact system {case+1}")

    result = {"status":"all exact finite checks passed", "date":"2026-09-29",
              "python":platform.python_version(), "sympy":s.__version__,
              "seed":20260929, "systems":len(CASES), "scalar_equalities_checked":CHECKS,
              "sharpness_coefficients":sharp,
              "critical_ancestors_hidden_example":list(map(str,ancestors)),
              "cases":CASES,
              "limitations":["Finite exact arithmetic only; not a Lean formalization.",
                 "Infinite convergence and universality theorems are proved in the article, not by this script.",
                 "No enumeration algorithm for arbitrary infinite real supports is asserted."]}
    dest = Path(__file__).resolve().with_name('results.json')
    dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k] for k in ['status','systems','scalar_equalities_checked','python','sympy']},indent=2))

if __name__ == '__main__':
    main()
