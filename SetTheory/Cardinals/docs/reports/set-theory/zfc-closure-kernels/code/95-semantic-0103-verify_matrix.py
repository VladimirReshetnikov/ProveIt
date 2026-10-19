#!/usr/bin/env python3
"""Exact countermodel to the fixed-falsity L+K propositional shortcut.

Only a theorem about the stated propositional schemas is asserted.
No first-order CP/GIC countermodel or blank-tape halting claim is made.
"""
from itertools import product
import json


def verify():
    rows = ((2, 2, 2), (2, 0, 2), (0, 0, 2))
    C = lambda a, b: rows[a][b]
    K = lambda a, b: C(a, C(b, a))
    S = lambda a, b, c: C(C(a, C(b, c)), C(C(a, b), C(a, c)))
    L = lambda a, b, c: C(C(C(c, 0), a), C(C(a, c), C(b, c)))
    schemas = {
        'L_fixed_F': (3, L),
        'K': (2, K),
        'ex_falso': (1, lambda a: C(0, a)),
        'double_negation_elimination': (1, lambda a: C(C(C(a, 0), 0), a)),
    }
    counts = {}
    for name, (arity, fn) in schemas.items():
        assignments = tuple(product(range(3), repeat=arity))
        assert all(fn(*v) == 2 for v in assignments), name
        counts[name] = len(assignments)
    for a, b in product(range(3), repeat=2):
        assert not (a == 2 and C(a, b) == 2) or b == 2
    assert C(1, 1) == 0
    assert S(1, 0, 1) == 0
    return {
        'status': 'PASS_EXACT_FINITE_MATRIX',
        'implication': rows,
        'designated': [2], 'relative_F': 0,
        'verified_instances': counts, 'modus_ponens_pairs': 9,
        'identity_counterexample': {'a': 1, 'value': C(1, 1)},
        'S_counterexample': {'a': 1, 'b': 0, 'c': 1, 'value': S(1, 0, 1)},
        'scope': 'The listed propositional schemas do not derive I or S under substitution and modus ponens.'
    }


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions must remain enabled.')
    print(json.dumps(verify(), indent=2))
