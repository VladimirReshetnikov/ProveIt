#!/usr/bin/env python3
"""Exact finite checks for Support Rank and Algebraic Freeness under Surreal Dilations.

Python 3.9+; SymPy is needed only for the rational-profile and explicit-relation
checks. These tests are not a formal verification of the infinite Hahn theorems.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations
import json
from pathlib import Path
import platform
import random
import time
from typing import Dict, Iterable, List, Sequence, Tuple

Exponent = Tuple[F, ...]
Polynomial = Dict[Exponent, F]


def rank(rows: Sequence[Sequence[F]]) -> int:
    if not rows:
        return 0
    a = [[F(x) for x in row] for row in rows]
    nr, nc, r = len(a), len(a[0]), 0
    for j in range(nc):
        p = next((i for i in range(r, nr) if a[i][j]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        v = a[r][j]
        a[r] = [x / v for x in a[r]]
        for i in range(nr):
            if i != r and a[i][j]:
                v = a[i][j]
                a[i] = [x - v*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == nr:
            break
    return r


def determinant(a: Sequence[Sequence[F]]) -> F:
    n = len(a)
    b = [[F(x) for x in row] for row in a]
    out = F(1)
    for j in range(n):
        p = next((i for i in range(j, n) if b[i][j]), None)
        if p is None:
            return F(0)
        if p != j:
            b[j], b[p] = b[p], b[j]
            out = -out
        v = b[j][j]
        out *= v
        for i in range(j+1, n):
            ratio = b[i][j]/v
            for l in range(j+1, n):
                b[i][l] -= ratio*b[j][l]
    return out


def multiply(p: Polynomial, q: Polynomial) -> Polynomial:
    result = defaultdict(F)
    for u, a in p.items():
        for v, b in q.items():
            result[tuple(x+y for x, y in zip(u, v))] += a*b
    return {u:a for u, a in result.items() if a}


def sign(perm: Sequence[int]) -> int:
    return (-1)**sum(perm[i] > perm[j]
                     for i in range(len(perm)) for j in range(i+1, len(perm)))


def polynomial_determinant(matrix: Sequence[Sequence[Polynomial]], dim: int) -> Polynomial:
    """Independent Leibniz expansion; does not use the greedy formula."""
    r = len(matrix)
    out = defaultdict(F)
    for perm in permutations(range(r)):
        product = {(F(0),)*dim: F(sign(perm))}
        for i, j in enumerate(perm):
            product = multiply(product, matrix[i][j])
        for u, a in product.items():
            out[u] += a
    return {u:a for u,a in out.items() if a}


def check_vector_case(data: Dict[Exponent, Tuple[F,...]], qs: Sequence[F]) -> int:
    r = len(qs)
    assert all(0 < x < y for x,y in zip(qs, qs[1:])) or r == 1 and qs[0] > 0
    exponents = sorted(data, reverse=True)
    greedy: List[Exponent] = []
    for u in exponents:
        if rank([data[v] for v in greedy]+[data[u]]) > len(greedy):
            greedy.append(u)
        if len(greedy) == r:
            break
    assert len(greedy) == r
    checked = 0
    for basis in combinations(exponents, r):
        if rank([data[u] for u in basis]) == r:
            assert all(g >= h for g,h in zip(greedy, basis))
            checked += 1
    dim = len(exponents[0])
    matrix = [[{tuple(q*x for x in u):q*c[j] for u,c in data.items() if c[j]}
               for j in range(r)] for q in qs]
    actual = polynomial_determinant(matrix, dim)
    expected_exp = tuple(sum(qs[r-1-i]*greedy[i][j] for i in range(r))
                         for j in range(dim))
    expected_coefficient = F((-1)**(r*(r-1)//2))*determinant([data[u] for u in greedy])
    for q in qs:
        expected_coefficient *= q
    assert actual and max(actual) == expected_exp
    assert actual[expected_exp] == expected_coefficient != 0
    return checked


def run() -> dict:
    rng = random.Random(20260923)
    counts = {"vector_determinants": 0, "independent_bases_compared": 0,
              "logarithmic_jacobians": 0, "telescoping_boundaries": 0,
              "rational_profiles": 0, "explicit_relations": 0,
              "characteristic_counterexamples": 0, "sign_counterexamples": 0}
    qs_pool = [F(1,3),F(1,2),F(1),F(3,2),F(2),F(3),F(4),F(5)]
    for r, cases in [(1,80),(2,100),(3,65),(4,12)]:
        for _ in range(cases):
            n = r+1+(rng.randrange(2) if r < 4 else 0)
            dim = rng.choice([1,2])
            while True:
                support = set()
                while len(support) < n:
                    support.add(tuple(F(rng.randrange(-7,8)) for _ in range(dim)))
                data = {u:tuple(F(rng.randrange(-3,4)) for _ in range(r)) for u in support}
                if rank(list(data.values())) == r:
                    break
            qs = sorted(rng.sample(qs_pool, r))
            counts['independent_bases_compared'] += check_vector_case(data, qs)
            counts['vector_determinants'] += 1
    for r, cases in [(1,40),(2,50),(3,35),(4,8)]:
        for _ in range(cases):
            while True:
                support = {tuple(F(rng.randrange(-3,4)) for _ in range(r)) for _ in range(r+2)}
                if rank(list(support)) == r:
                    break
            data = {}
            for u in support:
                a = F(rng.choice([-3,-2,-1,1,2,3]))
                data[u] = tuple(a*x for x in u)
            counts['independent_bases_compared'] += check_vector_case(data, sorted(rng.sample(qs_pool,r)))
            counts['logarithmic_jacobians'] += 1
    # Boundary term must NOT be dropped for finite truncations.
    for d in range(2,9):
        for n in range(1,21):
            U = {F(1,d**j):F(1) for j in range(n+1)}
            out = defaultdict(F)
            for e,a in U.items():
                out[d*e] += a
                out[e] -= a
            assert {e:a for e,a in out.items() if a} == {F(d):F(1), F(1,d**n):F(-1)}
            counts['telescoping_boundaries'] += 1
    import sympy as sp
    X,Y,Z = sp.symbols('X Y Z')
    f = X**2*Z + 2*X*Y - 3*Z + 5*Y + 7*X + 11
    variables = (X,Y,Z)
    rows = []
    for q in [1,2,4]:
        fq = f.subs(dict(zip(variables,[v**q for v in variables])), simultaneous=True)
        rows.append([v*sp.diff(fq,v) for v in variables])
    jac = sp.Poly(sp.expand(sp.det(sp.Matrix(rows))),X,Y,Z)
    leading = max(jac.terms(), key=lambda item:(sum(a*b for a,b in zip((1,4,16),item[0])), item[0]))
    assert leading == ((9,1,6),-96)
    counts['explicit_relations'] += 1
    profile_info=[]
    for P,Q,expected in [(X,X+Y,1),(X+Y,1+X*Y,2),(f,sp.Integer(1),3),
                         (X**2*Y**3+1,X**2*Y**3-2,1),
                         (sp.Integer(5),sp.Integer(2),0)]:
        H=[sp.Poly(sp.expand(Q*v*sp.diff(P,v)-P*v*sp.diff(Q,v)),X,Y,Z) for v in variables]
        powers=set().union(*(set(h.monoms()) for h in H))
        B=sp.Matrix([[h.coeff_monomial(u) for h in H] for u in sorted(powers)])
        actual_rank=B.rank()
        assert actual_rank == expected
        # A nonreduced representation must have exactly the same invariant.
        R=1+X+2*Y
        HH=[sp.Poly(sp.expand(Q*R*v*sp.diff(P*R,v)-P*R*v*sp.diff(Q*R,v)),X,Y,Z) for v in variables]
        pp=set().union(*(set(h.monoms()) for h in HH))
        BB=sp.Matrix([[h.coeff_monomial(u) for h in HH] for u in sorted(pp)])
        assert BB.rank()==expected
        profile_info.append({'P':str(P),'Q':str(Q),'rank':actual_rank})
        counts['rational_profiles'] += 2
    p,q,r = X+Y,X**2+Y**2,X**4+Y**4
    assert sp.expand(2*r-q**2-2*p**2*q+p**4)==0
    counts['explicit_relations'] += 1
    for prime in [2,3,5,7,11,13]:
        assert sp.Poly((X+Y)**prime-X**prime-Y**prime,X,Y,modulus=prime).is_zero
        counts['characteristic_counterexamples'] += 1
    symmetric=X+1/X+Y+1/Y
    assert sp.simplify(symmetric.subs({X:1/X,Y:1/Y}, simultaneous=True)-symmetric)==0
    counts['sign_counterexamples'] += 1
    return {'seed':20260923,'counts':counts,'total_named_test_cases':sum(v for k,v in counts.items() if k!='independent_bases_compared'),
            'worked_jacobian':{'auxiliary_weights':[1,4,16],'leading_exponent':list(leading[0]),
                               'leading_coefficient':int(leading[1]),'nonzero_terms':len(jac.terms())},
            'rational_profiles':profile_info,'sympy_version':sp.__version__,
            'scope':'Finite exact identities, determinants, greedy comparisons, and counterexamples only. Not a proof of infinite support, proper-class, or algebraic-freeness theorems.'}


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path('verification_results.json'))
    args=ap.parse_args()
    start=time.perf_counter()
    result=run()
    result['python_version']=platform.python_version()
    result['elapsed_seconds']=round(time.perf_counter()-start,3)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
