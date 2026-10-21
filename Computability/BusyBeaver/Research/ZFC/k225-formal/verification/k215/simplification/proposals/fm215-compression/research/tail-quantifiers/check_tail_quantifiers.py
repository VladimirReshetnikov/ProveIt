#!/usr/bin/env python3
"""Finite independent audit of the tail-quantifier obstruction.

The ordinary all-index proof is in tail_quantifier_obstruction.tex.
This is not a proof-assistant kernel certificate and does not assert a
countermodel of the full large-matrix seed theory.
"""
from itertools import product
import argparse
import json
from pathlib import Path


def run():
    n = 4
    worlds = tuple(product((0, 1), repeat=n))
    size = len(worlds)
    universe = (1 << size) - 1
    masks = []
    for i in range(n + 1):
        masks.append(tuple(sum(1 << j for j, f in enumerate(worlds)
                               if e[:i] == f[:i]) for e in worlds))

    def imp(a, b):
        return (universe ^ a) | b

    def atom(relation, a, b):
        return sum(1 << k for k, e in enumerate(worlds)
                   if relation(e[a], e[b]))

    def rel(a, b):
        return atom(lambda x, y: x < y, a, b)

    def eq(a, b):
        return atom(lambda x, y: x == y, a, b)

    def all_(i, p):
        # Formula support is limited to coordinates 0..3 in this audit.
        i = min(i, n)
        return sum(1 << w for w, mask in enumerate(masks[i])
                   if mask & p == mask)

    def ex(i, p):
        return universe ^ all_(i, universe ^ p)

    def pair(a, b):
        return (a + b) * (a + b + 1) // 2 + b

    def valid(p):
        assert p == universe

    # Each relation is reflexive, symmetric and transitive. Its universal
    # predicate transformer preserves top and arbitrary meets, establishing
    # normality and the distribution schema for all propositions at once.
    for i in range(n + 1):
        for w, mask in enumerate(masks[i]):
            assert mask & (1 << w)
            for v in range(size):
                if mask & (1 << v):
                    assert masks[i][v] == mask
        valid(all_(i, universe))

    # Relation composition = the relation with the smaller prefix.
    for i, j in product(range(n + 1), repeat=2):
        for w in range(size):
            composition = 0
            for v in range(size):
                if masks[i][w] & (1 << v):
                    composition |= masks[j][v]
            assert composition == masks[min(i, j)][w]

    checks = {'rho1': 0, 'rho3': 0, 'rho5': 0, 'merged_equality': 0,
              'high_vacuity': 0}
    for a, b in product(range(n), repeat=2):
        valid(ex(a, eq(a, b)))
        checks['rho1'] += 1
        for c in range(n):
            valid(imp(eq(a, b), imp(rel(c, a), rel(c, b))))
            checks['rho3'] += 1
            valid(imp(eq(c, a), imp(rel(c, b), rel(a, b))))
            checks['rho5'] += 1
            helper = 4 * pair(a, b) + 1
            assert helper > a and helper > b
            valid(imp(eq(c, a), imp(eq(c, b), all_(helper, eq(a, b)))))
            checks['merged_equality'] += 1
        for c in range(a + b + 1, a + b + 4):
            valid(imp(rel(a, b), all_(c, rel(a, b))))
            checks['high_vacuity'] += 1

    # Check all 65,536 propositions; no formula sampling is used here.
    qtable = [[all_(i, p) for p in range(universe + 1)] for i in range(n)]
    rho6_checks = 0
    commutation_checks = 0
    for p in range(universe + 1):
        for i in range(n):
            existential_of_universal = universe ^ qtable[i][universe ^ qtable[i][p]]
            valid(imp(existential_of_universal, p))
            rho6_checks += 1
            for j in range(n):
                assert qtable[i][qtable[j][p]] == qtable[min(i, j)][p]
                commutation_checks += 1

    missing = imp(rel(2, 3), all_(1, rel(2, 3)))
    assert missing != universe
    e = (0, 0, 0, 1)
    f = (0, 0, 0, 0)
    e_index, f_index = worlds.index(e), worlds.index(f)
    assert (rel(2, 3) >> e_index) & 1
    assert not ((all_(1, rel(2, 3)) >> e_index) & 1)
    assert masks[1][e_index] & (1 << f_index)
    assert not ((rel(2, 3) >> f_index) & 1)
    assert rel(0, 0) == 0
    return {
        'status': 'FINITE_TAIL_SEMANTICS_AUDIT_PASS',
        'worlds': size, 'propositions': universe + 1,
        'atomic_row_instances': checks,
        'rho6_instances': rho6_checks,
        'quantifier_compositions': commutation_checks,
        'counterexample': {'atom': [2, 3], 'binder': 1,
                          'world': list(e), 'accessible_falsifier': list(f)},
        'scope': 'Logical subsystem only. Full seed theory not modeled. '
                 'Arbitrary-index result is an ordinary proof, not kernel checked.'
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    raw = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(raw)
    print(raw, end='')
