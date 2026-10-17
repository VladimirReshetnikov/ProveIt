#!/usr/bin/env python3
"""Independent finite controls for the newly proposed canonical checker.

Does not establish consistency, completeness, a Lean result or a TM count.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE / 'code'))
import canonical254 as C
import symbolic254 as S


def main():
    arena = C.CanonicalArena()
    roots = [arena.literal(n) for n in range(2049)]
    assert len(set(roots)) == len(roots)
    constructor_controls = 0
    for a in range(32):
        for b in range(32):
            for tag in range(4):
                value = 2 * (a + b) * (a + b + 1) + 4 * b + tag
                built = arena.b(tag, arena.literal(a), arena.literal(b))
                assert built == arena.literal(value)
                constructor_controls += 1
    assert arena.b(0, 0, 0) == 0
    assert arena.literal(16) != 0  # Both encode truths, but not the same number.

    accepted = [
        (S.Raw(0), 0),
        (S.Raw(2, (0,), (S.Raw(0),)), 2),
        (S.Raw(2, (1,), (S.Raw(0),)), 6),
        (S.Raw(1, (0,), (S.Raw(0), S.Raw(0))), 0),
        (S.Raw(10, (0, 0, 0, 0)), 0),
    ]
    certificates = [C.make_certificate(p, n, quoted=False) for p, n in accepted]
    quoted_certificates = [C.make_certificate(p, n, quoted=True) for p, n in accepted]
    assert all(C.verify_certificate(c) for c in certificates + quoted_certificates)
    assert all(c['source_code'] == p.quote()
               for (p, _), c in zip(accepted, quoted_certificates))
    bad = []

    def reject(label, cert):
        assert not C.verify_certificate(cert), label
        bad.append(label)

    c = deepcopy(certificates[0]); c['nodes'].append(['b', 0, 0, 0])
    reject('noncanonical_zero_constructor', c)
    c = deepcopy(certificates[1]); c['nodes'].append(deepcopy(c['nodes'][1]))
    reject('duplicate_constructor_key', c)
    c = deepcopy(certificates[1]); c['nodes'][1][2] = 1
    reject('self_referential_arena', c)
    c = deepcopy(certificates[1]); c['nodes'][1][2] = -1
    reject('negative_arena_reference', c)
    c = deepcopy(certificates[1]); c['nodes'][1][1] = True
    reject('boolean_constructor_tag', c)
    c = deepcopy(certificates[1]); c['literals'][1]['value'] += 1
    reject('false_polynomial_literal_identity', c)
    c = deepcopy(certificates[1]); c['literals'][1]['parts'][0] = 1
    reject('self_referential_literal_witness', c)
    c = deepcopy(certificates[1]); c['proof_rows'][-1]['children'] = [1]
    reject('self_referential_proof_row', c)
    c = deepcopy(certificates[3]); c['proof_rows'][-1]['formula'] = 1
    reject('changed_mp_conclusion_reference', c)
    c = deepcopy(certificates[0]); c['proof_rows'][-1]['formula'] = False
    reject('boolean_formula_reference', c)
    c = deepcopy(certificates[0]); c['conclusion'] = True
    reject('boolean_target', c)
    c = deepcopy(certificates[0]); c['literals'][0]['value'] = False
    reject('boolean_initial_zero_value', c)
    c = deepcopy(certificates[0]); c['literals'][0]['node'] = False
    reject('boolean_initial_zero_reference', c)
    c = deepcopy(certificates[4]); c['proof_rows'][-1]['tag'] = 11
    c['proof_rows'][-1]['args'] = [0, 0, 0]
    reject('colliding_bundle_gate', c)
    c = deepcopy(certificates[0]); c['proof_rows'] = []
    reject('empty_proof', c)

    # Supply a fully valid literal witness for 16, but leave the proof at truth0.
    a = C.CanonicalArena(); a.literal(16)
    c = deepcopy(certificates[0]); c['nodes'] = [list(n) for n in a.nodes]
    c['literals'] = deepcopy(a.literals); c['conclusion'] = 16
    reject('semantic_truth_not_numeric_equality', c)

    c = deepcopy(quoted_certificates[0]); c['source_code'] += 1
    reject('changed_source_code', c)
    c = deepcopy(quoted_certificates[0]); c['proof_codes'][0] += 1
    reject('changed_proof_code', c)
    c = deepcopy(quoted_certificates[0]); c['source_code'] = 2; c['proof_codes'][0] = 2
    reject('consistent_forged_source_and_row_code', c)
    c = deepcopy(quoted_certificates[1]); c['proof_codes'][0] += 1
    reject('changed_premise_quote', c)
    c = deepcopy(quoted_certificates[1]); c['proof_codes'].pop(0)
    reject('truncated_proof_codes', c)
    c = deepcopy(quoted_certificates[1]); c['proof_codes'].append(1)
    reject('extra_proof_code', c)
    c = deepcopy(quoted_certificates[0]); del c['source_code']
    reject('missing_source_code', c)
    c = deepcopy(quoted_certificates[0]); del c['proof_codes']
    reject('missing_proof_codes', c)
    c = deepcopy(quoted_certificates[0]); c['source_code'] = True
    reject('boolean_source_code', c)
    c = deepcopy(quoted_certificates[0]); c['proof_codes'][0] = True
    reject('boolean_proof_code', c)

    def prohibited(*_a, **_k):
        raise AssertionError('Inverse/evaluation/parser called by verifier')
    disabled_records = {}
    for label, cases, disabled in [
        ('quoted', quoted_certificates, ('unpair', 'parse', 'build')),
        ('unquoted', certificates, ('unpair', 'pair', 'parse', 'build')),
    ]:
        old = {name: getattr(C, name) for name in disabled}
        old_s = {name: getattr(S, name) for name in disabled}
        try:
            for name in old:
                setattr(C, name, prohibited)
                setattr(S, name, prohibited)
            assert all(C.verify_certificate(c) for c in cases)
            disabled_records[label] = {'acceptances': len(cases),
                                       'disabled_functions': list(disabled)}
        finally:
            for name, value in old.items(): setattr(C, name, value)
            for name, value in old_s.items(): setattr(S, name, value)

    # A short DAG may contain an unused deep GEN chain before final truth0.
    # False tiny quote labels must be checked locally, never expanded globally.
    depth = 1000
    a = C.CanonicalArena()
    rows = [{'tag': 0, 'args': [], 'children': [], 'formula': 0}]
    current = 0
    for i in range(depth):
        current = a.b(2, 0, current)
        rows.append({'tag': 2, 'args': [0], 'children': [i], 'formula': current})
    rows.append({'tag': 0, 'args': [], 'children': [], 'formula': 0})
    attack = {'format': 'canonical-c254-v1', 'conclusion': 0,
              'nodes': [list(n) for n in a.nodes], 'literals': a.literals,
              'proof_rows': rows, 'source_code': 1, 'proof_codes': [1] * len(rows)}
    local_pair_calls = 0
    old_pair, old_quote_rows = C.pair, C.quote_rows

    def bounded_pair(x, y):
        nonlocal local_pair_calls
        local_pair_calls += 1
        assert max(x.bit_length(), y.bit_length()) <= 2
        return old_pair(x, y)

    try:
        C.quote_rows = prohibited
        assert all(C.verify_certificate(c) for c in quoted_certificates)
        C.pair = bounded_pair
        reject('unused_deep_gen_chain_with_false_small_quotes', attack)
        assert local_pair_calls == 1
    finally:
        C.pair, C.quote_rows = old_pair, old_quote_rows

    result = {
        'status': 'PASS',
        'scope': 'Independent finite controls and source inspection; no kernel proof or state saving',
        'literal_injectivity_range': [0, 2048],
        'constructor_integer_crosschecks': constructor_controls,
        'accepted_unquoted_certificates': len(certificates),
        'accepted_quoted_certificates': len(quoted_certificates),
        'rejected_corruptions': bad,
        'disabled_function_controls': disabled_records,
        'global_quote_reconstructor_disabled_acceptances': len(quoted_certificates),
        'unused_gen_chain_control': {'depth': depth,
                                     'local_forward_pair_calls_before_rejection': local_pair_calls},
        'source_sha256': {
            name: hashlib.sha256((BASE / 'code' / name).read_bytes()).hexdigest()
            for name in ('canonical254.py', 'symbolic254.py', 'extract_specs.py')
        },
    }
    target = BASE / 'data/canonical_audit_results.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
