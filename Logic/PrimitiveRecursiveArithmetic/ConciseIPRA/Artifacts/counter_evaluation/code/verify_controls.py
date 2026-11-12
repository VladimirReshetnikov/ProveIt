"""Check the matched scalar controls used only for source-size comparison.

The proposal itself has a larger independent validation suite, supplied
separately. This script checks raw root-rule elimination and representative
single-case normalized scalar proofs, including genuine hypothesis use.
"""

import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


raw = load('control_raw_ce5')
two = load('control_raw_two_case')
normal = load('control_zero_normal_eval')


def accepted(checker, certificate):
    try:
        return checker.verify(certificate) is True
    except Exception:
        return False


def remove_root(proof, context=(), scope=0):
    """Uniform raw CE5 -> two-case Eval proof transformation."""
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'u':
        return proof[:3] + [remove_root(proof[3], context, scope)]
    if tag == 'v':
        major = remove_root(proof[1], context, scope)
        minor = remove_root(proof[2], context, scope)
        s, t = raw.derive(proof[1], list(context), scope)
        b, r = raw.derive(proof[2], list(context), scope)
        if b == s:
            frame = [0, s, 0]
            return ['v', major, ['v', minor, ['r', frame]]]
        return ['v', major, minor]
    goal, data, branch = proof[1:]
    fresh = -scope - 1
    if tag == 'e':
        paired = raw.derive(data, list(context), scope)
        body = raw.opening(paired[0], fresh, 1)
        clause = (raw.opening(body, 0), body)
        translated_data = remove_root(data, context, scope)
    elif tag == 'i':
        body = raw.opening(goal[0], data, 1)
        eta = fresh if len(goal[0]) == 2 and data == 0 else 0
        clause = ([0, 0], raw.opening(body, eta))
        translated_data = data
    else:
        raise ValueError('unknown source proof')
    return [tag, goal, translated_data,
            remove_root(branch, tuple(context) + (clause,), scope + 1)]


def certificate(checker, proof):
    return {'goal': checker.derive(proof, [], 0), 'proof': proof}


def run():
    checks = []
    for path in sorted((ROOT / 'control_fixtures').glob('*.json')):
        data = json.loads(path.read_text())
        if path.name.startswith('reject_'):
            if accepted(raw, data) or accepted(two, data):
                raise RuntimeError('an invalid raw fixture was accepted')
            checks.append({'name': path.stem, 'status': 'rejected_both'})
        else:
            raw.verify(data)
            translated = dict(data, proof=remove_root(data['proof']))
            two.verify(translated)
            checks.append({'name': path.stem, 'status': 'root_eliminated'})

    zero = 0
    one = normal.successor(zero)
    two_n = normal.successor(one)
    positives = []
    for n in (zero, one, two_n):
        for h in (zero, 1, normal.successor(1)):
            prior = normal.rec(n, one, h)
            current = normal.rec(normal.successor(n), one, h)
            proof = ['v', ['r', prior], ['r', current]]
            data = certificate(normal, proof)
            if data['goal'] != [current, normal.opening(h, prior)]:
                raise RuntimeError('wrong scalar successor computation')
            positives.append(data)

    # Nontrivial induction: I(y,0;u.u)=0. The step uses its hypothesis.
    matrix = [[1, 0, 1], 0]
    goal = [matrix]
    hypothesis = ['u', 0, 0, ['r', 0]]
    current = normal.rec(normal.successor(-1), 0, 1)
    step = ['v', hypothesis, ['r', current]]
    induction = ['i', goal, 0, step]
    positives.append(certificate(normal, induction))
    for n in (zero, one, two_n):
        target = [normal.rec(n, 0, 1), 0]
        branch = ['u', 0, n, ['r', 0]]
        positives.append({'goal': target, 'proof': ['e', target, induction, branch]})
    for data in positives:
        normal.verify(data)
    checks.append({'name': 'zero_normal_positive_proofs', 'count': len(positives),
                   'status': 'accepted'})

    rejects = [
        {'goal': [False, False], 'proof': ['r', False]},
        {'goal': [-1, -1], 'proof': ['r', -1]},
        {'goal': [1, 1], 'proof': ['r', 1]},
        {'goal': [[0, 0, 1], [0, 0, 1]], 'proof': ['r', [0, 0, 1]]},
        {'goal': [0, one], 'proof': ['r', 0]},
        {'goal': [0, 0], 'proof': ['v', ['r', one], ['r', [one, 0, 1]]]},
        {'goal': [[0, 0]], 'proof': ['i', [[0, 0]], -1, ['r', 0]]},
    ]
    for data in rejects:
        if accepted(normal, data):
            raise RuntimeError('invalid zero-normal certificate was accepted')
    checks.append({'name': 'zero_normal_invalid_proofs', 'count': len(rejects),
                   'status': 'rejected'})
    result = {'checks': checks, 'unexpected_outcomes': 0}
    evidence = ROOT.parent / 'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence / 'control_validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    run()
