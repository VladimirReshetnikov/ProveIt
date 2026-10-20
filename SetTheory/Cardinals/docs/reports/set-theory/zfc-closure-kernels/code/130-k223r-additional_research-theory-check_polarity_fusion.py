#!/usr/bin/env python3
"""Generate and replay a uniform contextual-rewrite proof of K polarity fusion.

The local Boolean equivalences are truth-table checked. Congruence under
named universal quantification is the retained GEN/rho2 metatheorem, not a
new primitive axiom. This proves formula equivalence, not a TM state count.
"""
import argparse
import copy
import itertools
import json
from pathlib import Path

I = lambda x, y: ('imp', x, y)
N = lambda x: ('not', x)
Q = lambda a, x: ('all', a, x)
A = lambda x, y: ('and', x, y)
X = lambda a, x: ('exists', a, x)


def core(matrix):
    request = Q('b', I(matrix, X('b', A(matrix, 'R'))))
    support = X('a', A(matrix, Q('a', I('S', request))))
    return X('c', A(I(matrix, 'R'), Q('b', I('R', support))))


def start_formula():
    return A(core(N('psi')), A('rv', 'ev'))


def final_formula():
    t = Q('b', I('R', 'psi'))
    request = Q('b', I(t, 'psi'))
    h = Q('a', I('S', request))
    support = N(Q('a', I(h, 'psi')))
    closure = Q('b', I('R', support))
    u = Q('c', I(I(N('psi'), 'R'), N(closure)))
    return N(I('rv', I('ev', u)))


def children(f):
    if not isinstance(f, tuple):
        return ()
    return (2,) if f[0] in ('all', 'exists') else tuple(range(1, len(f)))


def find(f, predicate, path=()):
    if predicate(f):
        return path
    for k in children(f):
        answer = find(f[k], predicate, path + (k,))
        if answer is not None:
            return answer
    return None


def at(f, path):
    for k in path:
        if k not in children(f):
            raise ValueError('Path does not point into a formula context')
        f = f[k]
    return f


def replace(f, path, new):
    if not path:
        return new
    k, *rest = path
    if k not in children(f):
        raise ValueError('Invalid context')
    parts = list(f)
    parts[k] = replace(parts[k], rest, new)
    return tuple(parts)


def tagged(f, tag):
    return isinstance(f, tuple) and f[0] == tag


def local_rule(rule, f):
    if rule == 'rotate_three_conjuncts' and tagged(f, 'and') and tagged(f[2], 'and'):
        return A(f[2][1], A(f[2][2], f[1]))
    if rule == 'commute_conjunction' and tagged(f, 'and'):
        return A(f[2], f[1])
    if rule == 'expand_conjunction' and tagged(f, 'and'):
        return N(I(f[1], N(f[2])))
    if rule == 'expand_exists' and tagged(f, 'exists'):
        return N(Q(f[1], N(f[2])))
    if rule == 'double_negation' and tagged(f, 'not') and tagged(f[1], 'not'):
        return f[1][1]
    if rule == 'contraposition' and tagged(f, 'imp') and tagged(f[1], 'not') and tagged(f[2], 'not'):
        return I(f[2][1], f[1][1])
    raise ValueError('Rule does not match its stated subformula')


def propositional_value(f, env):
    if isinstance(f, str):
        return env[f]
    if f[0] == 'not':
        return not propositional_value(f[1], env)
    x, y = (propositional_value(t, env) for t in f[1:])
    if f[0] == 'imp':
        return not x or y
    if f[0] == 'and':
        return x and y
    raise ValueError('Unexpected connective in propositional schema')


def check_local_schemata():
    samples = {
        'rotate_three_conjuncts': A('x', A('y', 'z')),
        'commute_conjunction': A('x', 'y'),
        'expand_conjunction': A('x', 'y'),
        'double_negation': N(N('x')),
        'contraposition': I(N('x'), N('y')),
    }
    for name, lhs in samples.items():
        rhs = local_rule(name, lhs)
        for values in itertools.product((False, True), repeat=3):
            env = dict(zip(('x', 'y', 'z'), values))
            if propositional_value(lhs, env) != propositional_value(rhs, env):
                raise ValueError('Invalid propositional rewrite schema')
    # expand_exists is the definition of Exists, checked syntactically.
    if local_rule('expand_exists', X('a', 'x')) != N(Q('a', N('x'))):
        raise ValueError('Incorrect existential definition')
    return {'Boolean_schemata': len(samples), 'truth_assignments_per_schema': 8,
            'existential_definition': 'literal'}


def normalize(f, steps, allow_contraposition=True):
    def perform(rule, path):
        nonlocal f
        f = replace(f, path, local_rule(rule, at(f, path)))
        steps.append({'rule': rule, 'path': list(path)})
    while (path := find(f, lambda s: tagged(s, 'and') or tagged(s, 'exists'))) is not None:
        perform('expand_conjunction' if tagged(at(f, path), 'and') else 'expand_exists', path)
    while True:
        path = find(f, lambda s: tagged(s, 'not') and tagged(s[1], 'not'))
        if path is not None:
            perform('double_negation', path)
            continue
        path = find(f, lambda s: tagged(s, 'imp') and tagged(s[1], 'not') and tagged(s[2], 'not')) if allow_contraposition else None
        if path is not None:
            perform('contraposition', path)
            continue
        return f


def generate():
    f = start_formula()
    steps = [{'rule': 'rotate_three_conjuncts', 'path': []}]
    f = local_rule('rotate_three_conjuncts', f)
    while (path := find(f, lambda s: tagged(s, 'and') and s[1] == N('psi'))) is not None:
        f = replace(f, path, local_rule('commute_conjunction', at(f, path)))
        steps.append({'rule': 'commute_conjunction', 'path': list(path)})
    f = normalize(f, steps)
    if f != final_formula():
        raise ValueError('Generated rewrite sequence missed the target')
    return {'start': start_formula(), 'steps': steps, 'final': f,
            'scope': 'Uniform formula equivalence; arbitrary named binder labels. No machine state count.'}


def immutable(x):
    return tuple(immutable(y) for y in x) if isinstance(x, list) else x


def check(certificate):
    f = immutable(certificate['start'])
    if f != start_formula():
        raise ValueError('Incorrect starting K bundle')
    for step in certificate['steps']:
        path = step['path']
        f = replace(f, path, local_rule(step['rule'], at(f, path)))
    if f != immutable(certificate['final']) or f != final_formula():
        raise ValueError('Incorrect final polarity bundle')
    return len(certificate['steps'])


def negation_count(f):
    return (int(tagged(f, 'not')) + sum(negation_count(f[k]) for k in children(f)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).parent / 'evidence')
    args = parser.parse_args()
    local = check_local_schemata()
    certificate = generate()
    steps = check(certificate)
    old_fused = normalize(A(core('psi'), A('rv', 'ev')), [], allow_contraposition=False)
    if negation_count(old_fused) != 8 or negation_count(final_formula()) != 4:
        raise ValueError('Unexpected constructor counts')
    bad = copy.deepcopy(certificate)
    index = next(i for i, s in enumerate(bad['steps']) if s['rule'] == 'contraposition')
    del bad['steps'][index]
    try:
        check(bad)
    except (ValueError, IndexError, TypeError):
        tamper = 'rejected'
    else:
        raise ValueError('Missing contraposition tamper was accepted')
    receipt = {'status': 'PASS_UNIFORM_POLARITY_FUSION_REWRITE',
               'rewrite_steps': steps, 'local_equivalence_checks': local,
               'old_K224_template_negation_calls': 8,
               'new_polarity_core_last_negation_calls': 4,
               'missing_contraposition_tamper': tamper,
               'scope': certificate['scope']}
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / 'polarity_fusion_certificate.json').write_text(json.dumps(certificate, indent=2) + '\n')
    (args.output_dir / 'polarity_fusion_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
