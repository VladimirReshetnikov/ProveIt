#!/usr/bin/env python3
"""Exact finite checks for an actual-domain incidence-support obstruction.

This is not a SAT solver or an algorithmic lower-bound experiment.  It
checks the support and linear-algebra assertions used in the proof.
"""
from collections import Counter
from itertools import product
import json
import math


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def witness(n, q):
    require(1 <= q and 2*q < n, "invalid witness parameters")
    # Each quadratic original-variable monomial is a pair of bit positions.
    rows = [[(1 << i) | (1 << ((i+j) % n)) for j in range(1, q+1)]
            for i in range(n)]
    all_monomials = [m for row in rows for m in row]
    require(len(set(all_monomials)) == n*q, "original monomials collide")
    for selection in range(1 << n):
        support = set()
        for i in range(n):
            if selection >> i & 1:
                support.symmetric_difference_update(rows[i])
        require(len(support) == q*selection.bit_count(), "row support cancellation")

    # Original incidences are local to their test.  The center and q leaves
    # make n(q+1) separate incidence variables.
    inc_rows = [[(1 << (i*(q+1))) | (1 << (i*(q+1)+j))
                 for j in range(1, q+1)] for i in range(n)]
    exact_degree_support = set()
    for choices in product(range(q), repeat=n):
        mask = 0
        for i, choice in enumerate(choices):
            mask |= inc_rows[i][choice]
        require(mask.bit_count() == 2*n, "wrong full-choice degree")
        exact_degree_support.add(mask)
    require(len(exact_degree_support) == q**n, "wrong full-choice support")

    # Full V^0 polynomial: prod_i(1 - sum_j z_ii z_i,i+j).
    full_support = set()
    collapsed_coefficients = Counter()
    for choices in product(range(q+1), repeat=n):
        incidence_mask = original_mask = 0
        degree_rows = 0
        for i, choice in enumerate(choices):
            if choice:
                incidence_mask |= inc_rows[i][choice-1]
                original_mask |= rows[i][choice-1]
                degree_rows += 1
        require(incidence_mask not in full_support, "duplicate incidence monomial")
        full_support.add(incidence_mask)
        collapsed_coefficients[original_mask] += (-1)**degree_rows
    require(len(full_support) == (q+1)**n, "wrong constant-term support")
    collapsed_nonzero = sum(v != 0 for v in collapsed_coefficients.values())
    require(collapsed_nonzero <= 2**n, "invalid collapsed support")

    solutions = sum(all(sum((assignment & monomial) == monomial
                            for monomial in row) % 2 == 0 for row in rows)
                    for assignment in range(1 << n))
    return dict(n=n, q=q, distinct_original_quadratic_monomials=n*q,
                equations_linearly_independent=True,
                exact_degree_2n_incidence_monomials=q**n,
                full_V0_incidence_monomials=(q+1)**n,
                required_bits_for_one_network=math.ceil(n*math.log2(q)),
                collapsed_V0_nonzero_coefficients=collapsed_nonzero,
                solutions=solutions)


if __name__ == '__main__':
    checks = [witness(n, q) for n, q in [(5,1), (5,2), (7,2), (7,3), (9,2)]]
    print(json.dumps(dict(status='passed', cases=checks,
                         scope='Finite support and row-span checks only'), indent=2))
