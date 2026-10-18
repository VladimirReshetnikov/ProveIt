#!/usr/bin/env python3
"""Exhaustive finite countermodel for one proposed parameter deletion.

The verified 254 logic uses L(c,u,a,b) =
  ((c -> u) -> a) -> ((a -> c) -> (b -> c)).
Setting u to F saves a schematic parameter, but cannot inherit the classical
propositional completeness theorem.  The matrix below validates that
specialization, explosion and double-negation elimination, with modus ponens
preserving designation.  It refutes S and Peirce.

This does not refute a possible derivation using the full quantified theory.
It only blocks the direct propositional replacement argument.
"""
from itertools import product
import json

VALUES = range(3)
F = 0
DESIGNATED = 2
IMP = ((2, 2, 2), (2, 0, 2), (0, 0, 2))


def arrow(a, b):
    return IMP[a][b]


def neg(a):
    return arrow(a, F)


def special(c, a, b):
    return arrow(arrow(neg(c), a), arrow(arrow(a, c), arrow(b, c)))


def s_axiom(p, q, r):
    return arrow(arrow(p, arrow(q, r)), arrow(arrow(p, q), arrow(p, r)))


def peirce(p, q):
    return arrow(arrow(arrow(p, q), p), p)


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    assert all(a != DESIGNATED or arrow(a, b) != DESIGNATED or b == DESIGNATED
               for a, b in product(VALUES, repeat=2))
    assert all(special(c, a, b) == DESIGNATED
               for c, a, b in product(VALUES, repeat=3))
    assert all(arrow(F, a) == DESIGNATED for a in VALUES)
    assert all(arrow(neg(neg(a)), a) == DESIGNATED for a in VALUES)
    assert s_axiom(1, 0, 1) == 0
    assert peirce(1, 1) == 0
    print(json.dumps({
        'status': 'PASS',
        'matrix': IMP,
        'false_value': F,
        'designated_values': [DESIGNATED],
        'valid_schemes': ['L(c,F,a,b)', 'F -> a', '((a -> F) -> F) -> a'],
        'modus_ponens_preserves_designation': True,
        'specialized_axiom_valuations_checked': 27,
        'counterinstances': [
            {'scheme': 'S', 'p': 1, 'q': 0, 'r': 1, 'value': 0},
            {'scheme': 'Peirce', 'p': 1, 'q': 1, 'value': 0},
        ],
        'scope': 'Propositional parameter deletion is incomplete; no claim about the full quantified theory.'
    }, indent=2))


if __name__ == '__main__':
    main()
