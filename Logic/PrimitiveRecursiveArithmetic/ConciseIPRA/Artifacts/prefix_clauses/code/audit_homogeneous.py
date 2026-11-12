"""Targeted gate and certificate checks for the homogeneous alternative.

These finite checks do not establish the metatheory in the paper.
The numerical evaluator uses environments and performs no substitution.
"""
import hashlib
import json
import random
from pathlib import Path

import flat_homogeneous as H

ROOT = Path(__file__).resolve().parent
rng = random.Random(261111)


def number(n):
    return 0 if n == 0 else [number(n - 1)]


def term(scope, depth, fuel):
    if fuel == 0 or rng.randrange(3) == 0:
        return rng.randrange(-scope, depth + 1)
    if rng.randrange(2):
        return [term(scope, depth, fuel - 1)]
    return [number(rng.randrange(3)), term(scope, depth, fuel - 1),
            term(scope, depth + 1, fuel - 1)]


def value(a, free, bound=()):
    if type(a) is int:
        return 0 if a == 0 else free[-a - 1] if a < 0 else bound[a - 1]
    if len(a) == 1:
        return value(a[0], free, bound) + 1
    state = value(a[1], free, bound)
    for _ in range(value(a[0], free, bound)):
        state = value(a[2], free, (state,) + bound)
    return state


def rfl(t):
    return ['u', 0, t, []]


def zero(a, h):
    return ['v', rfl(a), rfl([0, a, h])]


def successor(c, a, h):
    return ['v', rfl([c, a, h]), rfl([[c], a, h])]


def join(p, q, source):
    return ['v', p, ['v', q, rfl([0, source, 1])]]


def retrieve_equation(s, t, index):
    h = H.sub(t, 0, 0, 1)
    left, right = [0, s, h], [[0], s, h]
    gated = ['u', index, [0], []]
    right_to_s = join(zero(s, h), gated, left)
    return join(successor(0, s, h), right_to_s, right)


def main():
    for _ in range(400):
        scope, k = rng.randrange(4), rng.randrange(4)
        a = [k, term(scope, 2 * k, 3), term(scope, 2 * k, 3)]
        assert H.formula(a, scope)
        gated = H.gate(a)
        at_zero = H.opening(gated, 0)
        assert H.formula(at_zero, scope) and at_zero[1] == at_zero[2]
        free = tuple(rng.randrange(4) for _ in range(scope))
        bound = tuple(rng.randrange(4) for _ in range(2 * k))
        for positive in (1, 2):
            opened = H.opening(gated, number(positive))
            assert H.formula(opened, scope)
            assert value(opened[1], free, bound) == value(a[1], free, bound)
            assert value(opened[2], free, bound) == value(a[2], free, bound)

    proofs = {
        'reflexivity': rfl([[0]]),
        'zero_computation': zero([0], [1]),
        'successor_computation': successor([0], 0, [1]),
        'compound_reflexivity': ['i', [2, 0, 0], [0],
                                 ['i', [1, 0, 0], [0], rfl(0)]],
    }
    step_source = [-1, 0, [1]]
    hypothesis = retrieve_equation(step_source, -1, 1)
    step = ['v', hypothesis, rfl([[-1], 0, [1]])]
    induction = ['i', [1, [1, 0, [1]], 1], 0, step]
    proofs['equation_induction_with_gate_retrieval'] = induction
    proofs['induction_specialization'] = [
        'e', induction, ['u', 1, number(3), zero(0, [1])]]
    for name, proof in proofs.items():
        goal = H.derive(proof, [[0, 1, 1]])
        H.verify({'goal': goal, 'proof': proof})
        (ROOT / 'examples' / ('homogeneous_' + name + '.json')).write_text(
            json.dumps({'goal': goal, 'proof': proof}, indent=2) + '\n')
    report = {
        'result': 'PASS', 'random_gate_formulas': 400,
        'positive_control_instances': 800,
        'accepted_closed_certificates': len(proofs),
        'nontrivial_certificate': 'Equation induction uses retrieval from its gated local assumption.',
        'checker_sha256': hashlib.sha256((ROOT / 'flat_homogeneous.py').read_bytes()).hexdigest(),
        'limits': 'Finite environment and certificate checks; no proof-assistant verification.'}
    (ROOT / 'evidence' / 'homogeneous_verification.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
