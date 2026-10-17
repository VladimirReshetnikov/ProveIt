#!/usr/bin/env python3
"""Finite controls for term254; not a formal theorem or a machine count."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path

import canonical254 as C
import symbolic254 as S
import term254 as T

BASE = Path(__file__).resolve().parents[1]


def convert_control(raw):
    """Append truth0 so even bundle controls need no integer materialization."""
    arena = C.CanonicalArena()
    root, valid, rows = S.build(raw, arena)
    assert valid
    for row in rows:
        del row['mp_equality']
    rows.append({'tag': 0, 'args': [], 'children': [], 'formula': 0})
    source = {'format': 'canonical-c254-v1', 'conclusion': 0,
              'nodes': [list(n) for n in arena.nodes],
              'literals': arena.literals, 'proof_rows': rows}
    assert C.verify_certificate(source)
    converted, zero_goal = T.from_canonical(source)
    assert zero_goal == 0
    converted['proof_rows'].pop()
    assert T.verify_certificate(converted, goal=root)
    return converted, root


def main():
    specimens = [S.Raw(0),
                 S.Raw(1, (0,), (S.Raw(0), S.Raw(0))),
                 S.Raw(2, (1,), (S.Raw(0),))]
    specimens += [S.Raw(tag, tuple(range(S.ARITY[tag]))) for tag in range(3, 11)]
    specimens.append(S.Raw(11, (0, 1, 2)))
    accepted = [convert_control(p) for p in specimens]
    assert {p.tag for p in specimens} == set(range(12))
    assert all(T.verify_certificate(c, goal=g) for c, g in accepted)
    assert not any(T.verify_certificate(c) for c, _ in accepted)
    # An adapter also accepts the exact quoted source format; it drops the quote.
    quoted = C.make_certificate(S.Raw(2, (1,), (S.Raw(0),)), 6)
    converted, target = T.from_canonical(quoted)
    assert T.verify_certificate(converted, goal=target)
    assert set(converted) == {'format', 'nodes', 'proof_rows'}

    bad = []

    def reject(label, cert, goal=None):
        assert not T.verify_certificate(cert, goal=goal), label
        bad.append(label)

    truth, _ = accepted[0]
    gen, gen_goal = accepted[2]
    bundle, bundle_goal = accepted[-1]
    c = deepcopy(truth); c['format'] = 'canonical-c254-v1'
    reject('wrong_format', c, 0)
    c = deepcopy(truth); c['nodes'][0] = ['n', 0]
    reject('numeric_zero_node', c, 0)
    c = deepcopy(truth); c['nodes'].append(['b', 0, 0, 0])
    reject('noncanonical_zero_constructor', c, 0)
    c = deepcopy(gen); c['nodes'].append(deepcopy(c['nodes'][1]))
    reject('duplicate_constructor_key', c, gen_goal)
    c = deepcopy(gen); c['nodes'][1][2] = 1
    reject('self_referential_node', c, gen_goal)
    c = deepcopy(gen); c['nodes'][1][2] = -1
    reject('negative_node_reference', c, gen_goal)
    c = deepcopy(gen); c['nodes'][1][1] = True
    reject('boolean_constructor_tag', c, gen_goal)
    c = deepcopy(gen); c['proof_rows'][-1]['args'] = [len(c['nodes'])]
    reject('out_of_range_argument', c, gen_goal)
    c = deepcopy(gen); c['proof_rows'][-1]['args'] = [True]
    reject('boolean_argument_reference', c, gen_goal)
    c = deepcopy(gen); c['proof_rows'][-1]['children'] = [1]
    reject('self_referential_proof', c, gen_goal)
    c = deepcopy(gen); c['proof_rows'][-1]['formula'] = 0
    reject('false_formula_reference', c, gen_goal)
    c = deepcopy(gen); c['proof_rows'][-1]['tag'] = True
    reject('boolean_rule_tag', c, gen_goal)
    c = deepcopy(truth); c['proof_rows'][-1]['formula'] = False
    reject('boolean_formula_reference', c, 0)
    c = deepcopy(truth); c['proof_rows'][-1]['args'] = [0]
    reject('incorrect_rule_arity', c, 0)
    c = deepcopy(truth); c['proof_rows'] = []
    reject('empty_proof', c, 0)
    c = deepcopy(bundle); c['proof_rows'][-1]['args'][2] = c['proof_rows'][-1]['args'][0]
    reject('first_bundle_inequality_collision', c, bundle_goal)
    c = deepcopy(bundle); c['proof_rows'][-1]['args'][2] = c['proof_rows'][-1]['args'][1]
    reject('second_bundle_inequality_collision', c, bundle_goal)
    c = deepcopy(gen); c['nodes'].pop()
    reject('missing_required_constructor', c, 0)
    reject('boolean_caller_goal', deepcopy(truth), False)
    reject('negative_caller_goal', deepcopy(truth), -1)
    reject('out_of_range_caller_goal', deepcopy(truth), len(truth['nodes']))
    # Certificate fields cannot override the trusted fixed falsity target.
    c = deepcopy(truth); c['nodes'].append(['b', 1, 0, 0]); c['goal'] = 0
    assert T.verify_certificate(c, goal=0)
    reject('certificate_cannot_choose_default_target', c)
    c = deepcopy(truth)
    c['nodes'].extend([['b', 1, 0, 0], ['b', 0, 1, 1]])
    reject('semantic_truth_not_numeric_equality', c, 2)
    c = deepcopy(accepted[1][0])
    c['nodes'].append(['b', 1, 0, 0])
    c['proof_rows'][-1]['args'] = [len(c['nodes'])-1]
    reject('false_modus_ponens_conclusion', c, len(c['nodes'])-1)

    depth = 1000
    arena = T.TermArena()
    rows = [{'tag': 0, 'args': [], 'children': [], 'formula': 0}]
    root = 0
    for i in range(depth):
        root = arena.b(2, 0, root)
        rows.append({'tag': 2, 'args': [0], 'children': [i], 'formula': root})
    deep = {'format': 'term-c254-v1', 'nodes': [list(n) for n in arena.nodes],
            'proof_rows': rows}
    assert T.verify_certificate(deep, goal=root)
    controls = accepted + [(converted, target), (deep, root)]

    def prohibited(*_args, **_kwargs):
        raise AssertionError('Numeric/producer function reached from ground verifier')

    patches = []
    for module in (C, S):
        for name in ('pair', 'unpair', 'parse', 'build', 'verify_certificate', 'make_certificate'):
            patches.append((module, name, getattr(module, name)))
    patches += [(C, 'quote_rows', C.quote_rows), (S.Raw, 'quote', S.Raw.quote)]
    for klass in (C.CanonicalArena, S.Arena):
        for name in ('materialize', 'literal'):
            patches.append((klass, name, getattr(klass, name)))
    try:
        for owner, name, _ in patches:
            setattr(owner, name, prohibited)
        assert all(T.verify_certificate(c, goal=g) for c, g in controls)
        assert not any(T.verify_certificate(c) for c, _ in controls)
    finally:
        for owner, name, old in reversed(patches):
            setattr(owner, name, old)

    result = {
        'status': 'PASS',
        'source_pin': 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
        'scope': 'Finite constructor-only controls; no formal proof, codec, TM, or new state bound',
        'all_rule_tags_checked': list(range(12)),
        'unquoted_canonical_conversions': len(accepted),
        'quoted_canonical_conversions': 1,
        'accepted_explicit_goal_controls': len(controls),
        'same_controls_rejected_at_fixed_falsity_goal': len(controls),
        'rejected_corruptions': bad,
        'deep_gen_control': {'depth': depth, 'arena_nodes': len(deep['nodes']),
                             'proof_rows': len(rows)},
        'disabled_function_controls': {
            'acceptances': len(controls),
            'disabled': ['pair', 'unpair', 'parse', 'build', 'numeric materialize',
                         'numeric literal decoder', 'Raw.quote', 'quote_rows',
                         'canonical/lazy certificate producers and verifiers']},
        'source_sha256': {
            name: hashlib.sha256((BASE/'code'/name).read_bytes()).hexdigest()
            for name in ('term254.py', 'check_term254.py', 'canonical254.py',
                         'symbolic254.py')},
    }
    (BASE/'data/term_certificate_results.json').write_text(json.dumps(result, indent=2)+'\n')
    (BASE/'data/example_term_bundle_control.json').write_text(json.dumps({
        'description': 'Positive bundle(0,1,2) control, not a derivation of falsity',
        'explicit_control_goal_id': bundle_goal, 'certificate': bundle}, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
