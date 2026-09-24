#!/usr/bin/env python3
"""Exact finite checks for the companion manuscript.

These checks verify finite algebra and examples. They do not prove infinite
well-ordering, strong summability, the extension theorem, or novelty.
Only the Python standard library is required.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
import json
from math import comb
from pathlib import Path

COUNTS: Counter[str] = Counter()

def check(category: str, assertion: bool) -> None:
    if not assertion:
        raise AssertionError(f"Failed {category}, after {COUNTS[category]} checks")
    COUNTS[category] += 1

# Bivariate polynomials are dictionaries (X-degree,Y-degree) -> Fraction.
def multiply(p: dict, q: dict) -> dict:
    out: dict = {}
    for (a, b), x in p.items():
        for (c, d), y in q.items():
            key = (a+c, b+d)
            out[key] = out.get(key, Q(0)) + x*y
    return {m: c for m, c in out.items() if c}

def evaluate(p: dict, x: Q, y: Q) -> Q:
    return sum((c*x**a*y**b for (a,b),c in p.items()), Q(0))

def subsets(s: frozenset) -> list[frozenset]:
    values = sorted(s)
    return [frozenset(c) for n in range(len(values)+1)
            for c in combinations(values, n)]

def run() -> dict:
    # Explicit countable-slope construction: finite products are exact.
    slopes = list(map(Q, [0,1,-1,2,-2,3,-3])) + [Q(1,2),Q(-1,2),Q(3,2)]
    p = {(0,0): Q(1)}
    for n, c in enumerate(slopes, 1):
        p = multiply(p, {(0,1): Q(1), (1,0): -c})
        check("homogeneous_products", all(a+b == n for a,b in p))
        check("homogeneous_products", evaluate(p,Q(0),Q(1)) == 1)
        for m, s in enumerate(slopes, 1):
            expected = Q(1)
            for c0 in slopes[:n]:
                expected *= s-c0
            value = evaluate(p,Q(1),s)
            check("polynomial_directions", value == expected)
            check("polynomial_directions", (value == 0) == (m <= n))
        check("polynomial_directions", evaluate(p,Q(1),Q(17)) != 0)

    # Cancellation in (X-Y)^n: blocks vanish but an individual term survives.
    for n in range(1,41):
        check("block_cancellation", sum((-1)**k*comb(n,k) for k in range(n+1)) == 0)
        check("block_cancellation", comb(n,0) == 1)

    # Nonclosed cone example: the exact difference is linear in n.
    vals = [Q(-3),Q(-1),Q(0),Q(1,5),Q(2)]
    for u,v in product(vals, repeat=2):
        for n in [1,2,7,19]:
            w = lambda k: k*u + k*k*v
            check("quadratic_weight_identity", w(n+1)-w(n) == u+(2*n+1)*v)
        if v > 0:
            N = max(1, int(abs(u)/(2*v))+2)
            check("quadratic_tail_certificate", u+(2*N+1)*v > 0)
        elif v < 0:
            N = max(1, int(abs(u)/(2*abs(v)))+2)
            check("quadratic_tail_certificate", u+(2*N+1)*v < 0)
        else:
            check("quadratic_tail_certificate", (u >= 0) == (u+(2*1+1)*v >= 0))
    for m in range(1,31):
        check("nonclosed_boundary_samples", Q(1,m) > 0)
        check("nonclosed_boundary_samples", -1+(2*(m+1)+1)*Q(1,m) > 0)

    # Semilinear period weights and integer-relation residual estimates.
    for q in product(vals, repeat=2):
        for p0 in [(1,1),(1,2),(2,1)]:
            b = (2,3)
            dot = lambda p: sum((p[i]*q[i] for i in range(2)),Q(0))
            for n in [0,1,6]:
                point = tuple(b[i]+n*p0[i] for i in range(2))
                check("semilinear_weight_identity", dot(point) == dot(b)+n*dot(p0))
    # delta_1=(1,3), delta_2=(-1,-2), quotient relation m=(n,n).
    for n in range(-40,41):
        m = (n,n)
        check("lattice_residual", m[0]-m[1] == 0)
        residual = 3*m[0]-2*m[1]
        check("lattice_residual", residual == n)
        check("lattice_residual", abs(residual) <= abs(m[0])+abs(m[1]))

    # All finite coordinate faces in a specified downward family, d=3.
    universe = frozenset(range(3))
    faces = subsets(universe)
    good = {frozenset(),frozenset({0}),frozenset({1}),frozenset({2}),frozenset({0,1})}
    bad_minimal = [B for B in faces if B not in good and
                   all(C in good for C in subsets(B) if C != B)]
    check("coordinate_face_realization", set(bad_minimal) == {frozenset({0,2}),frozenset({1,2})})
    for J in faces:
        check("coordinate_face_realization", (J in good) == (not any(B <= J for B in bad_minimal)))
        for B in bad_minimal:
            for n in [1,2,11]:
                alpha = tuple(n if j in B else 0 for j in range(3))
                survives = all(alpha[j] == 0 for j in universe-J)
                check("coordinate_face_realization", survives == (B <= J))

    # Degree-separated projective blocks: include EVERY coordinate multiplier.
    # Z_1 = [1:0:0]; Z_2 = the line Z=0. Test their block zero identities.
    degree = 1
    for block in [1,2]:
        gens = ([lambda c:c[1], lambda c:c[2]] if block == 1 else [lambda c:c[2]])
        assigned = []
        for gen in gens:
            for j in range(3):
                degree += 1
                assigned.append((gen,j,degree))
        for c in product([Q(-1),Q(0),Q(1)], repeat=3):
            if not any(c):
                continue
            kills_block = all(c[j]**(D-1)*gen(c) == 0 for gen,j,D in assigned)
            in_locus = (c[1] == c[2] == 0) if block == 1 else c[2] == 0
            check("projective_block_realization", kills_block == in_locus)

    return {
        "status": "passed",
        "total_assertions": sum(COUNTS.values()),
        "categories": dict(sorted(COUNTS.items())),
        "arithmetic": "integers and fractions.Fraction; no floating-point arithmetic",
        "scope": "Finite identities and finite example certificates only; not proofs of infinite theorems.",
        "formal_verification": False,
        "independent_peer_review": False,
        "priority_certified": False,
    }

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the JSON record to this path.")
    args = parser.parse_args()
    record = run()
    rendered = json.dumps(record,indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(rendered,encoding="utf-8")
    print(rendered,end="")

if __name__ == "__main__":
    main()
