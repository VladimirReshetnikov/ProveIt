#!/usr/bin/env python3
"""Finite diagnostics for the anchored-rank obstruction.

This is NOT a finite model of the native CP/GIC bundle. Its infinite
validation is proved in logic_obstructions.tex. No inference about a
Turing-machine state count follows from this script.
"""
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse
import json


@lru_cache(None)
def members(x):
    return tuple(i for i in range(x.bit_length()) if (x >> i) & 1)


@lru_cache(None)
def rank(x):
    return max((rank(y) + 1 for y in members(x)), default=0)


def rel(i, j, x, y):
    return rank(x) < rank(y) if j == 0 else x in members(y)


def regularized(x, y, carrier):
    # The exact equality-guarded R^(1,0), using coordinate values a,b.
    return any(a == x and b == y and rel(1, 0, a, b)
               for a in carrier for b in carrier)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path,
                   default=Path(__file__).with_name('anchored_rank_checks.json'))
    args = p.parse_args()
    carrier = tuple(range(16))  # exactly V_4 in Ackermann coding
    assert all(rank(x) < 4 for x in carrier)
    counts = dict(diagonal=0, retained_left_congruence=0,
                  regularization_identity=0, rank_subset_bound=0)
    for i, x in product(range(3), carrier):
        assert not rel(i, i, x, x)
        counts['diagonal'] += 1
    for a, b, c in product(range(3), repeat=3):
        # Source rho5(a,b,c): Eq(c,a) -> (Rel(c,b) -> Rel(a,b)).
        for s in product(carrier, repeat=3):
            assert not (s[c] == s[a] and rel(c, b, s[c], s[b])) or rel(a, b, s[a], s[b])
            counts['retained_left_congruence'] += 1
    for x, y in product(carrier, repeat=2):
        assert regularized(x, y, carrier) == (rank(x) < rank(y))
        counts['regularization_identity'] += 1
        if set(members(x)) <= set(members(y)):
            assert rank(x) <= rank(y)
            counts['rank_subset_bound'] += 1

    # GIC with matrix Eq(output,parameter), domain B={empty}, p={empty}.
    # Its native matrix code is 4*P(3,5)+3 = 167.
    matrix_code = 4 * (((3 + 5) * (3 + 5 + 1)) // 2 + 5) + 3
    assert matrix_code == 167
    domain = parameter = 1  # {empty}
    assert regularized(0, domain, carrier)
    rejected = []
    for collector in carrier:
        coverage = all(
            not regularized(x, domain, carrier) or all(
                y != parameter or any(
                    yp == parameter and regularized(yp, collector, carrier)
                    for yp in carrier)
                for y in carrier)
            for x in carrier)
        support = all(
            not regularized(y, collector, carrier) or any(y == parameter for _ in carrier)
            for y in carrier)
        assert not (coverage and support)
        if coverage:
            assert rank(collector) > 1
            assert regularized(0, collector, carrier)
            assert 0 != parameter
        rejected.append(dict(collector=collector, rank=rank(collector),
                             coverage=coverage, support=support))
    out = dict(
        status='PASS_FINITE_ANCHORED_RANK_DIAGNOSTICS',
        carrier='Ackermann 0..15 = V_4; not a model of the native CP/GIC bundle',
        infinite_proof='logic_obstructions.tex, Theorem 2',
        counts=counts,
        native_matrix_code=matrix_code,
        object_labels=dict(input=2, output_and_domain=3, parameter=5, collector=167),
        kernel_labels=dict(first=1, second=0),
        countervaluation=dict(domain=domain, parameter=parameter, domain_witness=0),
        rejected_collectors=rejected,
    )
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: out[k] for k in ('status', 'counts', 'native_matrix_code')}, indent=2))


if __name__ == '__main__':
    main()
