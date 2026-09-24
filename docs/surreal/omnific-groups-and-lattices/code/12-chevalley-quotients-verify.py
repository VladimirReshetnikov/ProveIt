#!/usr/bin/env python3
"""Exact finite checks accompanying the article; not a formal theorem prover.

Python 3.10+ and SymPy are required.  Output is written beside this script.
Run without -O, so that Python assertions remain enabled.
"""
from __future__ import annotations

import itertools
import json
import platform
import random
from collections import Counter
from pathlib import Path

import sympy as sp

COUNTS: Counter[str] = Counter()


def check(condition: bool, family: str) -> None:
    if not condition:
        raise AssertionError(f"Failed check in {family}")
    COUNTS[family] += 1


def E(n: int, i: int, j: int) -> sp.Matrix:
    out = sp.zeros(n)
    out[i - 1, j - 1] = 1
    return out


def bracket(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a * b - b * a


def exp_nil(a: sp.Matrix, x: sp.Expr) -> sp.Matrix:
    out, power = sp.eye(a.rows), sp.eye(a.rows)
    for j in range(1, a.rows + 1):
        power = power * a
        if power == sp.zeros(a.rows):
            return out
        out += power * x**j / sp.factorial(j)
    raise ValueError("Matrix is not nilpotent within the expected bound")


def comm(a: sp.Matrix, b: sp.Matrix, x: sp.Expr, y: sp.Expr) -> sp.Matrix:
    return exp_nil(a, x) * exp_nil(b, y) * exp_nil(a, -x) * exp_nil(b, -y)


def matrix_equal(a: sp.Matrix, b: sp.Matrix, family: str) -> None:
    check(all(sp.expand(c) == 0 for c in a - b), family)


def symbolic_checks() -> None:
    r, s = sp.symbols("r s")
    a, b, c = E(3, 1, 2), E(3, 2, 3), E(3, 1, 3)
    matrix_equal(comm(a, b, r, s), exp_nil(c, r * s), "A2 symbolic identities")
    n = E(4, 1, 2) - E(4, 4, 3)
    m = E(4, 1, 4) + E(4, 2, 3)
    ell, k = E(4, 1, 3), E(4, 2, 4)
    matrix_equal(comm(n, m, r, s), exp_nil(ell, 2 * r * s), "C2 symbolic identities")
    matrix_equal(comm(k, n, r, s), exp_nil(m, -r*s) * exp_nil(ell, -r*s*s),
                 "C2 symbolic identities")
    matrix_equal(comm(n, m, r, s/2), exp_nil(ell, r*s), "C2 symbolic identities")

    a = E(7, 1, 2) + 2*E(7, 3, 4) + E(7, 4, 5) + E(7, 6, 7)
    b = E(7, 2, 3) + E(7, 5, 6)
    c = bracket(a, b)
    d = bracket(a, c)/2
    e = bracket(a, d)/3
    f = bracket(b, e)
    matrix_equal(comm(a, c, r, s),
                 exp_nil(d, 2*r*s) * exp_nil(e, 3*r*r*s) * exp_nil(f, -3*r*s*s),
                 "G2 symbolic identities")
    matrix_equal(comm(b, e, r, s), exp_nil(f, r*s), "G2 symbolic identities")
    matrix_equal(comm(a, c, r, s/2),
                 exp_nil(d, r*s) * exp_nil(e, sp.Rational(3, 2)*r*r*s)
                 * exp_nil(f, -sp.Rational(3, 4)*r*s*s), "G2 symbolic identities")
    fa = E(7, 2, 1) + E(7, 4, 3) + 2*E(7, 5, 4) + E(7, 7, 6)
    fb = E(7, 3, 2) + E(7, 6, 5)
    ha, hb = bracket(a, fa), bracket(b, fb)
    relations = [(bracket(ha, a), 2*a), (bracket(ha, b), -3*b),
                 (bracket(hb, a), -a), (bracket(hb, b), 2*b),
                 (bracket(a, fb), sp.zeros(7)), (bracket(b, fa), sp.zeros(7)),
                 (bracket(ha, hb), sp.zeros(7))]
    for lhs, rhs in relations:
        matrix_equal(lhs, rhs, "G2 Cartan and cross relations")
    z = b
    for _ in range(4):
        z = bracket(a, z)
    matrix_equal(z, sp.zeros(7), "G2 Serre relations")
    matrix_equal(bracket(b, bracket(b, a)), sp.zeros(7), "G2 Serre relations")
    for root in [a, b, c, d, e, f, fa, fb]:
        for j in range(1, 8):
            divided = root**j / sp.factorial(j)
            check(all(v.q == 1 for v in divided), "Integral divided powers")

    e2, f2 = E(2, 1, 2), E(2, 2, 1)
    h2 = bracket(e2, f2)
    for lhs, rhs in [(bracket(h2, e2), 2*e2), (bracket(h2, f2), -2*f2),
                     (bracket(e2, f2), h2)]:
        matrix_equal(lhs, rhs, "sl2 bracket-lattice recovery")


Vector = tuple[int, ...]


def add(a: Vector, b: Vector, i: int = 1, j: int = 1) -> Vector:
    return tuple(i*x + j*y for x, y in zip(a, b))


def norm(a: Vector) -> int:
    return sum(x*x for x in a)


def classical(kind: str, n: int) -> set[Vector]:
    dim = n + 1 if kind == "A" else n
    roots: set[Vector] = set()
    for i in range(dim):
        for j in range(i + 1, dim):
            for s, t in itertools.product([-1, 1], repeat=2):
                if kind == "A" and s == t:
                    continue
                v = [0]*dim
                v[i], v[j] = 2*s, 2*t
                roots.add(tuple(v))
    if kind in ("B", "C"):
        size = 2 if kind == "B" else 4
        for i in range(dim):
            for s in [-1, 1]:
                v = [0]*dim
                v[i] = size*s
                roots.add(tuple(v))
    return roots


def exceptional() -> dict[str, set[Vector]]:
    f4 = classical("B", 4) | set(itertools.product([-1, 1], repeat=4))
    e8 = classical("D", 8) | {
        v for v in itertools.product([-1, 1], repeat=8) if sum(x < 0 for x in v) % 2 == 0
    }
    e7 = {v for v in e8 if v[6] + v[7] == 0}
    e6 = {v for v in e8 if v[5] + v[7] == 0 and v[6] + v[7] == 0}
    g2: set[Vector] = set()
    for i in range(3):
        for j in range(3):
            if i != j:
                v = [0]*3
                v[i], v[j] = 1, -1
                g2.add(tuple(v))
        for s in [-1, 1]:
            v = [-s]*3
            v[i] = 2*s
            g2.add(tuple(v))
    return {"G2": g2, "F4": f4, "E6": e6, "E7": e7, "E8": e8}


def witness(roots: set[Vector], target: Vector) -> str:
    for a in sorted(roots):
        b = add(target, a, 1, -1)
        if b not in roots:
            continue
        positive = {(i, j) for i in range(1, 4) for j in range(1, 4)
                    if add(a, b, i, j) in roots}
        p = 0
        while add(b, a, 1, -(p+1)) in roots:
            p += 1
        la, lb, lt = norm(a), norm(b), norm(target)
        if positive == {(1, 1)} and la == lb == lt and p == 0:
            return "A2"
        if positive == {(1, 1)} and la == lb and lt == 2*la and p == 1:
            return "B2 long"
        if positive == {(1, 1), (1, 2)} and la == 2*lb and lt == lb and p == 0:
            return "B2 short"
        if positive == {(1, 1), (2, 1), (1, 2)} and la == lb == lt and p == 1:
            return "G2 short"
    raise AssertionError(f"No rank-two witness for {target}")


def root_checks() -> dict[str, dict[str, int]]:
    systems: dict[str, set[Vector]] = {}
    for n in range(2, 9):
        for kind in ["A", "B", "C"]:
            systems[f"{kind}{n}"] = classical(kind, n)
    for n in range(4, 9):
        systems[f"D{n}"] = classical("D", n)
    systems.update(exceptional())
    expected = {"G2": 12, "F4": 48, "E6": 72, "E7": 126, "E8": 240}
    results = {}
    for name, roots in systems.items():
        if name in expected:
            check(len(roots) == expected[name], "Exceptional root counts")
        found = Counter()
        for target in sorted(roots):
            found[witness(roots, target)] += 1
            check(True, "Root reconstruction witnesses")
        results[name] = dict(sorted(found.items()))
    return results


def rank_one_checks() -> None:
    rng = random.Random(20260923)
    t = sp.symbols("T")
    ident = sp.eye(2)
    e = E(2, 1, 2)

    def constant(nonupper: bool = False) -> sp.Matrix:
        while True:
            a, b, c = [rng.randint(-3, 3) for _ in range(3)]
            out = sp.Matrix([[1, a], [0, 1]]) * sp.Matrix([[1, 0], [b, 1]]) \
                  * sp.Matrix([[1, c], [0, 1]])
            if not nonupper or out[1, 0] != 0:
                return out

    for _ in range(80):
        length = rng.randint(1, 5)
        gs = [constant()] + [constant(True) for _ in range(length - 1)] + [constant()]
        degrees, params, leaders = [], [], []
        for _ in range(length):
            degree = rng.randint(1, 4)
            lead = rng.choice([-3, -2, -1, 1, 2, 3])
            lower = sum(rng.randint(-2, 2)*t**j for j in range(1, degree))
            degrees.append(degree)
            leaders.append(lead)
            params.append(lead*t**degree + lower)
        product = gs[0]
        for j in range(length):
            product = (product * (ident + params[j]*e) * gs[j+1]).applyfunc(sp.expand)
        top_degree = sum(degrees)
        top = product.applyfunc(lambda p: sp.Poly(p, t).nth(top_degree))
        predicted = sp.prod(leaders) * sp.prod(g[1, 0] for g in gs[1:-1]) * gs[0] * e * gs[-1]
        matrix_equal(top, predicted, "Rank-one top coefficients")
        check(predicted != sp.zeros(2), "Rank-one nonvanishing")
        check(sp.expand(product.det()) == 1, "Rank-one determinants")


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without Python optimization flags")
    symbolic_checks()
    coverage = root_checks()
    rank_one_checks()
    result = {
        "status": "passed",
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "total_checks": sum(COUNTS.values()),
        "checks_by_family": dict(COUNTS),
        "root_system_coverage": coverage,
        "scope": "Exact finite algebra only: not verification of class theory, Hahn support closure, "
                 "all infinite ranks, or the universal-quotient theorems.",
    }
    destination = Path(__file__).resolve().with_name("verification_results.json")
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
