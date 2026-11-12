"""Independent finite check of the one-body checker's binder-sensitive gate.

This checks intended numerical values using an independent environment
semantics, rather than comparing gate() against a duplicate implementation.
It does not verify the theorem-level completeness or soundness proof.
"""

import importlib.util
import itertools
import json
import sys


def evaluate(term, bound=(), parameters=(2, 3)):
    if type(term) is int:
        if term == 0:
            return 0
        return bound[term - 1] if term > 0 else parameters[-term - 1]
    if len(term) == 2:
        return 1 + evaluate(term[1], bound, parameters)
    counter, seed, step = term
    result = evaluate(seed, bound, parameters)
    for _ in range(evaluate(counter, bound, parameters)):
        result = evaluate(step, (result,) + tuple(bound), parameters)
    return result


def leaf(formula):
    while len(formula) == 1:
        formula = formula[0]
    return formula


def wrap(equation, depth):
    for _ in range(depth):
        equation = [equation]
    return equation


def check(checker_path):
    spec = importlib.util.spec_from_file_location('body_checker_audit', checker_path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checks = 0
    for depth in range(4):
        atoms = [0, -1, -2] + list(range(1, 2 * depth + 1))
        terms = atoms + [[0, term] for term in atoms]
        for seed in atoms:
            for body in [0, 1] + list(range(2, 2 * depth + 2)):
                terms += [[[0, 0], seed, body],
                          [[0, [0, 0]], seed, [0, body]]]
        for index, term in enumerate(terms):
            formula = wrap([term, terms[-index - 1]], depth)
            assert checker.formula(formula, 2)
            gated = checker.gate(formula)
            assert checker.formula(gated, 2, 1)
            for bound in itertools.product(range(2), repeat=2 * depth):
                for value in (0, 1, 2):
                    expected = ((0, 0) if value == 0 else
                                tuple(evaluate(t, bound) for t in leaf(formula)))
                    actual = tuple(evaluate(t, tuple(bound) + (value,))
                                   for t in leaf(gated))
                    assert actual == expected
                    witness = 0 if value == 0 else [0, 0] if value == 1 else [0, [0, 0]]
                    opened = checker.opening(gated, witness)
                    assert checker.formula(opened, 2)
                    assert tuple(evaluate(t, bound) for t in leaf(opened)) == expected
                    checks += 1
    return {'gate_endpoint_and_scope_checks': checks, 'status': 'PASS'}


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: python3 audit_gate_scopes.py PATH_TO_CHECKER')
    print(json.dumps(check(sys.argv[1]), sort_keys=True))
