#!/usr/bin/env python3
"""Exact trace tests, nonmaximal-order examples, and an S-integer budget.

These verify finite algebra identities. General theorems are proved in the
report. No arithmetic Galois realization or formal Lean proof is certified.
"""
from __future__ import annotations
import argparse
from functools import reduce
from itertools import product
from math import gcd
import json
from pathlib import Path
from sympy import Matrix, ZZ, eye
from sympy.matrices.normalforms import smith_normal_form

def flat(M):
    return [int(M[i, j]) for i in range(M.rows) for j in range(M.cols)]

def relations(pairs):
    d = pairs[0][0].rows
    units = []
    for i in range(d):
        for j in range(d):
            E = Matrix.zeros(d)
            E[i, j] = 1
            units.append(E)
    return Matrix.vstack(*[Matrix.hstack(*[Matrix(flat(X*A-B*X)) for X in units])
                           for A, B in pairs])

def smith_factors(M):
    D = smith_normal_form(M, domain=ZZ)
    return [abs(int(D[i, i])) for i in range(M.cols)]

def val(n, p):
    if not n:
        return None
    a = 0
    while n % p == 0:
        n //= p
        a += 1
    return a

def brute_count(M, modulus):
    rows = [[int(x) for x in row] for row in M.tolist()]
    return sum(all(sum(x*y for x, y in zip(row, X)) % modulus == 0
                   for row in rows)
               for X in product(range(modulus), repeat=M.cols))

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    I = eye(2)
    E12, E21 = Matrix([[0, 1], [0, 0]]), Matrix([[0, 0], [1, 0]])
    A, B = I+E12, I+E21
    basis = [I, A, B, A*B]
    gram = Matrix([[int((X*Y).trace()) for Y in basis] for X in basis])
    assert gram.det() == -1
    report = {"status": "all exact checks passed",
              "scope": "finite algebra; not a formal proof or Galois realization"}
    P = Matrix([[1, 2], [0, 1]])
    conj = lambda X: P*X*P.inv()
    for X in basis:
        for Y in basis:
            assert (X*Y).trace() == (conj(X)*conj(Y)).trace()
            for G in (A, B, I):
                assert (G*X*Y).trace() == (conj(G)*conj(X)*conj(Y)).trace()
    report["finite_trace_test"] = {
        "basis_words": ["1", "u", "v", "uv"],
        "basis_determinant": int(Matrix.hstack(*[Matrix(flat(X)) for X in basis]).det()),
        "trace_gram_determinant": int(gram.det()),
        "pair_tests": 16, "generator_triple_tests": 48,
        "theoretical_max_word_length_rank_two": 7,
        "actual_max_word_length_this_basis": 5,
        "warning": "Generators must generate G or the joint representation image."
    }
    obstruction = []
    for p, a, c in [(3, 1, 1), (3, 2, 1), (3, 1, 2), (5, 3, 2)]:
        Ac, Bc = I+p**c*E12, I+p**c*E21
        M = relations([(Ac, Ac), (Bc, Bc), (I, (1+p**a)*I)])
        factors = smith_factors(M)
        assert factors == [p**min(a,c)]*3+[p**a]
        order_basis = [I, p**c*E12, p**c*E21, Matrix([[p**(2*c), 0], [0, 0]])]
        order_smith = smith_factors(Matrix.hstack(*[Matrix(flat(X)) for X in order_basis]))
        assert order_smith == [1, p**c, p**c, p**(2*c)]
        brute = []
        if p == 3:
            for n in (1, 2):
                count = brute_count(M, p**n)
                length = min(n, a)+3*min(n, a, c)
                assert count == p**length
                brute.append({"n": n, "kernel_size": count, "length": length})
        assert val(2*p**a, p) == a
        obstruction.append({
            "p": p, "trace_depth_a": a, "image_depth_c": c,
            "relation_smith_factors": factors, "matrix_order_smith_factors": order_smith,
            "order_colength": 4*c, "order_conductor_exponent": 2*c,
            "finite_level_length": "min(n,a)+3*min(n,a,c)",
            "supremum_length": a+3*min(a,c), "exhaustive_checks": brute})
    report["nonmaximal_order_examples"] = obstruction
    q = 25
    discrepancies = [(1-q)*int(X.trace()) for X in basis]
    ideal_generator = reduce(gcd, map(abs, discrepancies))
    assert ideal_generator == 24
    factors = smith_factors(relations([(A,A), (B,B), (I,q*I)]))
    assert factors == [1,1,1,24]
    report["common_denominator_example"] = {
        "coefficient_ring": "Z[1/5]", "trace_discrepancies": discrepancies,
        "ideal_generator": 24, "excluded_rational_primes": [5],
        "nonzero_local_lengths": {"2": 3, "3": 1}, "denominator_product": 24,
        "rank_two_scalar_bound_product": 576, "relation_smith_factors": factors,
        "arithmetic_realization_claimed": False}
    text = json.dumps(report, indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")

if __name__ == "__main__":
    main()
