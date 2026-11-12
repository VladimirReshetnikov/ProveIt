"""Checked deterministic-discharge -> explicit witness-discharge translation.

This producer is untrusted. The proposed checker validates its source, the
unchanged old checker validates its output, and an independently implemented
inherited kernel replays the output after a syntax-only conversion.
There is no claim of an executable inverse translation.
"""
from pathlib import Path
import importlib.util
import json
import sys

from inherited_reference_kernel import opening, replace_parameter, check as replay

ROOT = Path(__file__).resolve().parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


candidate = load('deterministic_discharge', ROOT / 'code/checker.py')
control = load('explicit_witness_discharge', ROOT / 'reference/witness_discharge_checker.py')


def selection(matrix, scope):
    fresh = -scope - 1
    body = opening(matrix, fresh, 1)
    base = opening(body, 0)
    row = opening(body, [0, 0])
    extracted = base == [0, 0] and len(row) == 2 and row[0] == fresh
    return body, base, row[1] if extracted else fresh, extracted


def to_old(goal, proof, context, scope):
    tag = proof[0]
    if tag == 'u':
        index, target, premise = proof[1:]
        base, body = context[index]
        return ['u', index, target, to_old(base, premise, context, scope) if base else None]
    if tag == 'i':
        witness, branch = proof[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        base = opening(body, eta)
        expected = opening(body, [0, fresh])
        return ['i', witness, to_old(expected, branch, context + [([], base)], scope + 1)]
    if tag == 'e':
        matrix, formula, major, branch = proof[1:]
        body, base, target, extracted = selection(matrix, scope)
        local = context + [(base, body)]
        if extracted:
            equation = ['u', len(context), [0, 0], ['u', 0, 0, None]]
        else:
            equation = ['u', 0, -scope - 1, None]
        return ['e', matrix, formula, target,
                to_old([matrix], major, context, scope), equation,
                to_old(formula, branch, local, scope + 1)]
    raise ValueError('unknown deterministic proof instruction')


def old_to_independent(goal, proof, context, scope):
    """Reintroduce explicit Refl and goal annotations for the old replay kernel."""
    tag = proof[0]
    if tag == 'u':
        index, target, premise = proof[1:]
        if index == 0:
            return ['r', target]
        base, body = context[index]
        return ['u', index - 1, target,
                old_to_independent(base, premise, context, scope) if base else ['r', 0]]
    if tag == 'i':
        witness, branch = proof[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        base = opening(body, eta)
        expected = opening(body, [0, fresh])
        return ['i', goal, witness,
                old_to_independent(expected, branch, context + [([], base)], scope + 1)]
    if tag == 'e':
        matrix, formula, target, major, equation, branch = proof[1:]
        body = opening(matrix, -scope - 1, 1)
        local = context + [(opening(body, 0), body)]
        return ['e', goal,
                old_to_independent([matrix], major, context, scope),
                old_to_independent([-scope - 1, target], equation, local, scope + 1),
                old_to_independent(formula, branch, local, scope + 1)]
    raise ValueError('unknown explicit proof instruction')


def translate_checked(data):
    candidate.check(data)
    context = [([], [1, 1])]
    result = {'goal': data['goal'], 'proof': to_old(data['goal'], data['proof'], context, 0)}
    control.check(result)
    independently_encoded = {'goal': result['goal'],
                             'proof': old_to_independent(result['goal'], result['proof'], context, 0)}
    replay(independently_encoded)
    return result


if __name__ == '__main__':
    result = translate_checked(json.load(sys.stdin))
    json.dump(result, sys.stdout, separators=(',', ':'))
    sys.stdout.write('\n')
