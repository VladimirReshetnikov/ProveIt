#!/usr/bin/env python3
"""Independent exhaustive check of the three-valued U=A obstruction.

Uses symbolic formula syntax and an evaluator, independently of the mutable
C++ finite-model search.  All generators are checked on the full carrier;
the actual native gates can only reduce the instance family.
"""
import itertools
import json
from pathlib import Path

CARRIER = range(3)
TRUTH, FALSE, DESIGNATED = 2, 0, {2}
TABLES = {
    'I': ((1, 2, 2), (2, 2, 2), (1, 1, 2)),
    'R': ((1, 1, 0), (1, 0, 0), (1, 1, 0)),
    'E': ((0, 0, 0), (0, 0, 0), (0, 0, 0)),
    'Q': ((1, 1, 2), (1, 1, 2), (1, 1, 2)),
}

def op(name):
    return lambda a, b: (name, a, b)

I, R, E, Q = map(op, 'IREQ')
def neg(a): return I(a, FALSE)
def exists(a, b): return neg(Q(a, neg(b)))
def req(b, k, m):
    return Q(b, I(m, neg(Q(b, I(m, neg(R(b, k)))))))
def clos(a, b, k, m):
    inside = I(Q(k, I(R(k, a), R(k, b))), req(b, k, m))
    return Q(b, I(R(b, k), neg(Q(a, I(m, neg(Q(a, inside)))))))
def bundle(a, b, c):
    left = I(R(a, b), Q(c, R(a, b)))
    right = Q(c, I(clos(a, b, c, c), neg(req(b, c, c))))
    return neg(I(left, right))

a, b, c = 'a', 'b', 'c'
SCHEMATA = {
    'rho1': exists(a, E(a, b)),
    'rho2': I(Q(a, I(b, c)), I(Q(a, b), Q(a, c))),
    'rho3': I(E(a, b), I(R(c, a), R(c, b))),
    'rho4': I(Q(a, Q(b, c)), Q(b, Q(a, c))),
    'rho5': I(E(c, a), I(R(c, b), R(a, b))),
    'rho6': I(exists(a, Q(a, b)), b),
    'G': I(E(c, a), I(E(c, b), Q(R(a, b), E(a, b)))),
    'rho8_U_equals_A': I(I(I(c, a), a), I(I(a, c), I(b, c))),
    'bundle': bundle(a, b, c),
}

def value(formula, env):
    if isinstance(formula, int): return formula
    if isinstance(formula, str): return env[formula]
    name, left, right = formula
    return TABLES[name][value(left, env)][value(right, env)]

def variables(formula):
    if isinstance(formula, int): return set()
    if isinstance(formula, str): return {formula}
    return variables(formula[1]) | variables(formula[2])

def check():
    assert TRUTH in DESIGNATED and FALSE not in DESIGNATED
    assert TABLES['I'][TRUTH][TRUTH] == TRUTH
    assert TABLES['R'][TRUTH][TRUTH] == FALSE
    mp = gen = 0
    for x, y in itertools.product(CARRIER, repeat=2):
        if x in DESIGNATED and TABLES['I'][x][y] in DESIGNATED:
            assert y in DESIGNATED, ('MP', x, y)
        if y in DESIGNATED:
            assert TABLES['Q'][x][y] in DESIGNATED, ('GEN', x, y)
        mp += 1
        gen += 1
    checked = {}
    for name, formula in SCHEMATA.items():
        names = sorted(variables(formula))
        outcomes = []
        for values in itertools.product(CARRIER, repeat=len(names)):
            env = dict(zip(names, values))
            result = value(formula, env)
            assert result in DESIGNATED, (name, env, result)
            outcomes.append(result)
        checked[name] = {'assignments': len(outcomes), 'values': sorted(set(outcomes))}
    return {
        'status': 'PASS',
        'claim': 'Every generator of the native calculus with rho8 restricted to U=A is designated; falsity is not.',
        'carrier': list(CARRIER), 'designated': sorted(DESIGNATED),
        'truth': TRUTH, 'falsity': FALSE, 'tables': TABLES,
        'modus_ponens_pairs': mp, 'generalization_pairs': gen,
        'schemata': checked,
    }

if __name__ == '__main__':
    result = check()
    rendered = json.dumps(result, indent=2) + '\n'
    Path(__file__).with_name('diagonal_matrix_check.json').write_text(rendered)
    print(rendered, end='')
