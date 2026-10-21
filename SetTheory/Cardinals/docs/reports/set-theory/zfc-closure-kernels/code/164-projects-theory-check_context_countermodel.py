#!/usr/bin/env python3
"""Finite matrix and its lift to selected total raw-code projector families.

The lift uses four low-code seeds; it is not a model of all native rows or
the set-theory bundle.  See projection_basis.tex for the universal proof.
"""
from itertools import product
from functools import lru_cache
from math import isqrt
import json
from pathlib import Path

TABLE = ((3, 3, 2, 3), (3, 3, 3, 3), (0, 3, 3, 3), (0, 1, 2, 3))
VALUES = range(4)
TRUTH = 3


def imp(a, b):
    return TABLE[a][b]


def rho(a, b, c, u):
    return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))


def context_values(word, u):
    current = {u}
    for letter in reversed(word):
        current = {imp(a, x) if letter == 'L' else imp(x, a)
                   for a in current for x in VALUES}
    return current


def native_imp(a, b):
    return 4 * ((a + b) * (a + b + 1) // 2 + b)


def native_rho(a, b, c, u):
    return native_imp(native_imp(native_imp(c, u), a),
                      native_imp(native_imp(a, c), native_imp(b, c)))


def children(n):
    q = n // 4
    diagonal = (isqrt(8*q + 1) - 1) // 2
    right = q - diagonal*(diagonal + 1)//2
    return diagonal-right, right


def projection(n, word):
    for letter in word:
        n = children(n)[letter == 'R']
    return n


@lru_cache(None)
def raw_value(n):
    if n < 4:
        return (3, 0, 1, 2)[n]
    left, right = children(n)
    assert left < n and right < n
    return imp(raw_value(left), raw_value(right))


def check():
    if not __debug__:
        raise RuntimeError('Run this checker without -O: assertions are the checks.')
    assert imp(TRUTH, TRUTH) == TRUTH
    assert all(imp(TRUTH, a) != TRUTH for a in VALUES if a != TRUTH)
    assert all(rho(a, b, c, TRUTH) == TRUTH for a, b, c in product(VALUES, repeat=3))
    families = {}
    for word in ('', 'L', 'R', 'RRR', 'LL', 'LR', 'LLR', 'LLLR'):
        bad = [(a, b, c, u) for u in VALUES for a in context_values(word, u)
               for b, c in product(VALUES, repeat=2) if rho(a, b, c, u) != TRUTH]
        families[word or 'epsilon'] = {'valid': not bad, 'first_failure': bad[0] if bad else None}
    assert all(families[word]['valid'] for word in ['epsilon', 'L', 'R', 'RRR'])
    basis = {
        'I': (1, lambda a: imp(a, a)),
        'K': (2, lambda a, b: imp(a, imp(b, a))),
        'Peirce': (2, lambda a, b: imp(imp(imp(a, b), a), a)),
        'cd59': (3, lambda a, b, c: imp(imp(a, b), imp(imp(imp(a, c), a), b))),
        'B': (3, lambda a, b, c: imp(imp(a, b), imp(imp(b, c), imp(a, c)))),
        'S': (3, lambda a, b, c: imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))),
    }
    tested = {}
    for name, (arity, formula) in basis.items():
        failures = [args for args in product(VALUES, repeat=arity) if formula(*args) != TRUTH]
        tested[name] = {'valid': not failures, 'first_failure': failures[0] if failures else None}
    assert all(tested[name]['valid'] for name in ['I', 'K', 'Peirce', 'cd59'])
    assert not tested['B']['valid'] and not tested['S']['valid']
    assert rho(1, 0, 2, 0) == 2
    # These bounded checks supplement the universal low-code-escape lifting
    # proof in the report.  All arithmetic and comparisons are exact.
    homomorphism_cases = 0
    for a, b in product(range(64), repeat=2):
        assert raw_value(native_imp(a, b)) == imp(raw_value(a), raw_value(b))
        homomorphism_cases += 1
    raw_family_cases = 0
    for a, b, c in product(range(4096), VALUES, VALUES):
        for word in ('', 'L', 'R', 'RRR'):
            u = projection(a, word)
            assert rho(raw_value(a), b, c, raw_value(u)) == TRUTH
            raw_family_cases += 1
    raw_witness = native_rho(2, 1, 3, 1)
    assert raw_value(1) == 0 != TRUTH
    assert raw_value(raw_witness) == 2 != TRUTH
    return {
        'verified': True, 'table': TABLE, 'designated_value': TRUTH,
        'zero_alias_and_MP': True, 'zero_fourth_family': True,
        'context_families': families, 'basis': tested,
        'unrestricted_rho8_failure': {'A': 1, 'B': 0, 'C': 2, 'U': 0, 'value': 2},
        'raw_code_lift': {
            'seeds': {'h(0)': 3, 'h(1)': 0, 'h(2)': 1, 'h(3)': 2},
            'recursion_for_n_at_least_4': 'h(n)=TABLE[h(left(n))][h(right(n))], irrespective of the native tag',
            'proper_prefix_low_seed_escape': 'A proper prefix equal to 1,2,3 forces the final projected code to0; constant-zero fourth-family then applies',
            'valid_total_families': ['constant0', 'epsilon', 'L', 'R', 'RRR'],
            'implication_homomorphism_cases': homomorphism_cases,
            'raw_family_cases': raw_family_cases,
            'unrestricted_numeric_witness': {'A': 2, 'B': 1, 'C': 3, 'U': 1,
                                             'rho_code': raw_witness, 'value': 2},
            'scope_of_finite_checks': 'Supplement to the universal lifting argument; not an exhaustive check over all natural codes'
        },
        'scope': 'Models truth, MP, and the listed total raw-code rho8 projector families, also I/K/Peirce/cd59. It refutes recovery of unrestricted rho8 using only these resources. It is not a model of all retained native rows, GEN, or the theory bundle, and does not rule out equiconsistency with ZFC after adding such axioms.',
    }


if __name__ == '__main__':
    result = check()
    Path(__file__).with_name('context_countermodel.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
