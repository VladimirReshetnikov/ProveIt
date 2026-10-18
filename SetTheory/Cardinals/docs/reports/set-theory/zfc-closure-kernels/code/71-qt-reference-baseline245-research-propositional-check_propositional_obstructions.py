#!/usr/bin/env python3
"""Verify finite obstructions to proposed three-parameter logical shortcuts.

The matrices prove failure of propositional completeness for the stated
axiom bases. They are not countermodels of the whole CP/GIC set theory.
No third-party dependencies.
"""
from itertools import product
import json


def audit_matrix(name, rows, axioms, bad_formula, witness):
    n = len(rows)
    top, bottom = n - 1, 0
    assert all(len(row) == n and all(0 <= x < n for x in row) for row in rows)

    def C(a, b):
        return rows[a][b]

    def K(a, b):
        return C(a, C(b, a))

    def S(a, b, c):
        return C(C(a, C(b, c)), C(C(a, b), C(a, c)))

    def L(a, b, c, u):
        return C(C(C(c, u), a), C(C(a, c), C(b, c)))

    predicates = {
        'identity': (1, lambda a: C(a, a)),
        'K': (2, K),
        'ex_falso': (1, lambda a: C(bottom, a)),
        'DNE': (1, lambda a: C(C(C(a, bottom), bottom), a)),
        'L_u_F': (3, lambda a, b, c: L(a, b, c, bottom)),
        'L_u_a': (3, lambda a, b, c: L(a, b, c, a)),
        'L_u_b': (3, lambda a, b, c: L(a, b, c, b)),
        'L_u_c': (3, lambda a, b, c: L(a, b, c, c)),
    }
    checked = {}
    for ax in axioms:
        arity, evaluate = predicates[ax]
        cases = list(product(range(n), repeat=arity))
        assert all(evaluate(*v) == top for v in cases), (name, ax)
        checked[ax] = len(cases)
    for a, b in product(range(n), repeat=2):
        assert not (a == top and C(a, b) == top) or b == top
    value = {'K': K, 'S': S}[bad_formula](*witness)
    assert value != top
    return {
        'name': name, 'implication': rows, 'designated_values': [top],
        'falsity_value': bottom, 'verified_axiom_instances': checked,
        'modus_ponens_pairs_checked': n*n,
        'refuted_formula': bad_formula, 'witness': list(witness), 'witness_value': value,
        'scope': 'The listed propositional bases are incomplete; no claim about CP/GIC equiconsistency.'
    }


def main():
    fixed_false = audit_matrix(
        'Fixed fourth parameter F, even with ex falso and DNE',
        [[2, 2, 2], [2, 1, 2], [0, 0, 2]],
        ['L_u_F', 'ex_falso', 'DNE'], 'K', (1, 1))
    variable_identification = audit_matrix(
        'Identifying u with a, b, or c; Lukasiewicz three-valued matrix',
        [[2, 2, 2], [1, 2, 2], [0, 1, 2]],
        ['identity', 'K', 'ex_falso', 'DNE', 'L_u_a', 'L_u_b', 'L_u_c'],
        'S', (1, 1, 0))
    print(json.dumps({'status': 'PASS', 'certificates': [fixed_false, variable_identification]}, indent=2))


if __name__ == '__main__':
    main()
