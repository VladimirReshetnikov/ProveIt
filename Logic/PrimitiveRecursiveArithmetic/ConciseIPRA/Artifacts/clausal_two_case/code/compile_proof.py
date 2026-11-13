"""Untrusted certificate compiler from CE5 with three Eval cases to two.

The output is accepted only after the standalone two-case checker verifies it.
The legacy converter is for the pinned raw_clausal regression fixtures.
"""
import control_three_case as source
import checker as target


def eliminate(proof, context, scope):
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'u':
        _, j, t, p = proof
        return ['u', j, t, eliminate(p, context, scope)]
    if tag == 'v':
        _, p, q = proof
        _, s, t = source.derive(p, context, scope)
        _, b, r = source.derive(q, context, scope)
        p = eliminate(p, context, scope)
        q = eliminate(q, context, scope)
        if b == s:
            frame = ['i', ['z'], s, ['v', 1]]
            q = ['v', q, ['r', frame]]
        return ['v', p, q]
    fresh = ['v', -scope - 1]
    if tag == 'e':
        _, p, q = proof
        paired = source.derive(p, context, scope)
        body = source.opening(paired[1], fresh, 1)
        clause = (source.opening(body, ['z']), body)
        return ['e', eliminate(p, context, scope),
                eliminate(q, context + [clause], scope + 1)]
    _, b, t, p = proof
    body = source.opening(b, t, 1)
    eta = fresh if b[0] == '=' and t == ['z'] else ['z']
    clause = (['=', ['z'], ['z']], source.opening(body, eta))
    return ['i', b, t, eliminate(p, context + [clause], scope + 1)]


def translate(data):
    source.verify(data)
    result = {'goal': data['goal'], 'proof': eliminate(data['proof'], [], 0)}
    target.verify(result)
    return result


def legacy_term(a):
    if type(a) is int:
        return ['z'] if a == 0 else ['v', a]
    if len(a) == 2:
        return ['s', legacy_term(a[1])]
    n, seed, body = a
    return ['i', legacy_term(n), legacy_term(seed), legacy_term(body)]


def legacy_formula(a):
    if len(a) == 1:
        return ['d', legacy_formula(a[0])]
    return ['=', legacy_term(a[0]), legacy_term(a[1])]


def legacy_proof(p):
    tag = p[0]
    if tag == 'r':
        return ['r', legacy_term(p[1])]
    if tag == 'u':
        return ['u', p[1], legacy_term(p[2]), legacy_proof(p[3])]
    if tag == 'v':
        return ['v', legacy_proof(p[1]), legacy_proof(p[2])]
    if tag == 'e':
        return ['e', legacy_proof(p[2]), legacy_proof(p[3])]
    return ['i', legacy_formula(p[1])[1], legacy_term(p[2]), legacy_proof(p[3])]


def from_legacy(data):
    from importlib.util import module_from_spec, spec_from_file_location
    from pathlib import Path
    path = Path(__file__).resolve().parents[1] / 'reference/upstream/code/clausal_eval.py'
    spec = spec_from_file_location('pinned_legacy_checker', path)
    legacy = module_from_spec(spec)
    spec.loader.exec_module(legacy)
    legacy.verify(data)
    result = {'goal': legacy_formula(data['goal']), 'proof': legacy_proof(data['proof'])}
    source.verify(result)
    return result


if __name__ == '__main__':
    import argparse
    import json
    import sys
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--legacy', action='store_true',
                        help='read a pinned raw_clausal-format certificate')
    args = parser.parse_args()
    data = json.load(sys.stdin)
    if args.legacy:
        data = from_legacy(data)
    json.dump(translate(data), sys.stdout)
    print()
