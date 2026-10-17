#!/usr/bin/env python3
"""Finite QA of proof-carrying, lookup-free C254 constructor circuits."""
from copy import deepcopy
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import platform
import time

import term_circuits as V
import term_paths as P
import test_paths as Q
import check_term254 as CT
import symbolic254 as S
import canonical254 as C
import term254 as T

BASE = Path(__file__).resolve().parent
TABLES = V.load_templates(BASE/'source50/data/spec254.json')


def from_term(cert):
    """Producer only: reuse an interned source50 cert and add fixed-circuit IDs."""
    out = P.from_term(cert)
    out['format'] = V.FORMAT
    arena = P.LookupArena(out['nodes'], {'lookup_records': 0})
    for row in out['proof_rows']:
        if row['tag'] >= 3:
            circuit = TABLES[row['tag']]
            roots = list(row['args']) + [0]
            ids = []
            for tag, left, right in circuit.steps:
                root = arena.b(tag, roots[left], roots[right])
                ids.append(root)
                roots.append(root)
            assert roots[circuit.root] == row['formula']
            row['constructor_ids'] = ids
    return out


def main():
    started = time.monotonic()
    tests, rejects, controls = [], [], []
    specimens = [S.Raw(0), S.Raw(1, (0,), (S.Raw(0), S.Raw(0))),
                 S.Raw(2, (1,), (S.Raw(0),))]
    specimens += [S.Raw(tag, tuple(range(S.ARITY[tag]))) for tag in range(3, 11)]
    specimens += [S.Raw(11, (0, 1, 2))]
    originals = []
    for raw in specimens:
        term, goal = CT.convert_control(raw)
        cert = from_term(term)
        assert V.verify_certificate(cert, TABLES, goal=goal)
        assert not V.verify_certificate(cert, TABLES)
        controls.append((cert, goal))
        originals.append((term, goal))
    tests.append('all12 exact source50 controls convert and verify; all12 reject at fixedF')

    # Compare the independently transcribed fixed-circuit compiler with original
    # source50 apply, including every collision of parameters from{0,1,2}.
    template_cases = 0
    assert V.ARITY == S.ARITY
    for rule, circuit in TABLES.items():
        name = 'bundle' if rule == 11 else 'rho' + str(rule - 2)
        for args in product(range(3), repeat=circuit.arity):
            arena = Q.ProducerArena()
            literals = [0, arena.b(1, 0, 0), arena.b(2, 0, 0)]
            roots = [literals[n] for n in args]
            expected = arena.apply(name, roots)
            values = roots + [0]
            for tag, left, right in circuit.steps:
                values.append(arena.b(tag, values[left], values[right]))
            assert values[circuit.root] == expected
            template_cases += 1
    tests.append('261 fixed-template comparisons against original source50, including all parameter collisions over0/1/2')

    # Duplicate result copies are useful accepted encodings, not only unused junk.
    gen, goal = deepcopy(controls[2])
    gen['nodes'].append(deepcopy(gen['nodes'][goal]))
    new_goal = len(gen['nodes']) - 1
    gen['proof_rows'][-1]['formula'] = new_goal
    assert V.verify_certificate(gen, TABLES, goal=new_goal)
    old = deepcopy(gen); old['format'] = P.FORMAT
    assert not P.verify_certificate(old, goal=new_goal)
    controls.append((gen, new_goal))
    tests.append('GEN may name a non-first duplicate result, which lookup prototype rejects')
    leaf, goal = deepcopy(controls[3])
    leaf['nodes'].append(deepcopy(leaf['nodes'][goal]))
    new_goal = len(leaf['nodes']) - 1
    leaf['proof_rows'][-1]['formula'] = new_goal
    circuit = TABLES[3]
    assert circuit.root == circuit.arity + len(circuit.steps)
    leaf['proof_rows'][-1]['constructor_ids'][-1] = new_goal
    assert V.verify_certificate(leaf, TABLES, goal=new_goal)
    controls.append((leaf, new_goal))
    tests.append('schema may name a non-first duplicate output with a valid local witness')
    assert V.is_falsity([['z'], ['b', 1, 0, 0], ['b', 1, 0, 0]], 1)
    assert V.is_falsity([['z'], ['b', 1, 0, 0], ['b', 1, 0, 0]], 2)
    assert not V.is_falsity([['z'], ['b', 3, 0, 0]], 1)
    tests.append('fixedF endpoint recognizes either copy, rejects other tag; no firstF lookup')

    # Both attacks use the exact complete bundle constructor circuit.
    for equal_to_a in (True, False):
        cert, target = Q.bundle_fixture(equal_to_a)
        cert['format'] = 'term-c254-v1'
        # Add circuit IDs directly without producer path-search rejection.
        cert['format'] = V.FORMAT
        arena = P.LookupArena(cert['nodes'], {'lookup_records': 0})
        row = cert['proof_rows'][0]
        values = row['args'] + [0]
        ids = []
        for tag, left, right in TABLES[11].steps:
            result = arena.b(tag, values[left], values[right])
            ids.append(result); values.append(result)
        row['constructor_ids'] = ids
        assert values[TABLES[11].root] == target
        stats = {}
        assert not V.verify_certificate(cert, TABLES, goal=target, stats=stats)
        reason = 'bundle_gate_1' if equal_to_a else 'bundle_gate_2'
        assert stats['reason'] == reason
        rejects.append(reason + '_pointer_distinct_equal_value')

    # Import the prior genuinely deep bundle as producer input, not as checker.
    deep = json.loads((BASE/'deep-bundle-control.json').read_text())
    source = deep['certificate']; source['format'] = 'term-c254-v1'
    deep_cert = from_term(source)
    deep_goal = deep['trusted_control_goal']
    stats = {}
    assert V.verify_certificate(deep_cert, TABLES, goal=deep_goal, stats=stats)
    assert stats['path_edges'] == 2048
    assert stats['template_searches'] == 0 and stats['arena_uniqueness_comparisons'] == 0
    assert stats['circuit_steps'] == len(TABLES[11].steps)
    controls.append((deep_cert, deep_goal))
    tests.append('2048-edge exact bundle uses only62 explicit constructor checks after local validation')

    def reject(label, cert, goal):
        ss = {}
        assert not V.verify_certificate(cert, TABLES, goal=goal, stats=ss), label
        rejects.append(label)
    for label, mutate in [
        ('missing_constructor_witness', lambda c: c['proof_rows'][-1].pop('constructor_ids')),
        ('truncated_circuit', lambda c: c['proof_rows'][-1]['constructor_ids'].pop()),
        ('extra_circuit_step', lambda c: c['proof_rows'][-1]['constructor_ids'].append(0)),
        ('wrong_circuit_wire', lambda c: c['proof_rows'][-1]['constructor_ids'].__setitem__(0, 0)),
        ('out_of_range_circuit_id', lambda c: c['proof_rows'][-1]['constructor_ids'].__setitem__(0, len(c['nodes']))),
        ('boolean_circuit_id', lambda c: c['proof_rows'][-1]['constructor_ids'].__setitem__(0, True)),
    ]:
        cert = deepcopy(controls[3][0]); mutate(cert); reject(label, cert, controls[3][1])
    cert = deepcopy(controls[1][0])
    cert['nodes'].append(['b', 1, 0, 0]); bad_goal = len(cert['nodes']) - 1
    cert['proof_rows'][-1]['args'] = [bad_goal]
    cert['proof_rows'][-1]['formula'] = bad_goal
    reject('false_MP_major', cert, bad_goal)
    cert = deepcopy(controls[2][0]); cert['proof_rows'][-1]['formula'] = 0
    reject('false_GEN_shape', cert, 0)
    cert = deepcopy(controls[0][0]); cert['nodes'].append(['b', 0, 0, 0])
    reject('forbidden_zero_alias', cert, 0)
    cert = deepcopy(controls[11][0]); cert['proof_rows'][-1]['gate_paths'][0] += [0]
    reject('trailing_gate_path', cert, controls[11][1])
    cert = deepcopy(controls[0][0]); cert['goal'] = 0
    cert['templates'] = {'all_rules': 'true'}
    assert V.verify_certificate(cert, TABLES, goal=0)
    assert not V.verify_certificate(cert, TABLES)
    tests.append('certificate cannot override trusted templates or fixed default goal')

    def prohibited(*_args, **_kwargs):
        raise AssertionError('search/arithmetic/producer called by circuit verifier')
    patches = [(P, 'verify_certificate', P.verify_certificate),
               (P, 'find_path', P.find_path), (P, 'from_term', P.from_term),
               (P.LookupArena, 'b', P.LookupArena.b),
               (T, 'verify_certificate', T.verify_certificate),
               (T, 'from_canonical', T.from_canonical),
               (V, 'compile_templates', V.compile_templates),
               (V, 'load_templates', V.load_templates)]
    for module in (S, C):
        for name in ('pair', 'unpair', 'parse', 'build', 'verify_certificate', 'make_certificate'):
            patches.append((module, name, getattr(module, name)))
    for klass in (S.Arena, C.CanonicalArena):
        for name in ('materialize', 'literal', 'intern', 'b', 'apply'):
            patches.append((klass, name, getattr(klass, name)))
    try:
        for owner, name, _ in patches:
            setattr(owner, name, prohibited)
        for cert, goal in controls:
            assert V.verify_certificate(cert, TABLES, goal=goal)
            assert not V.verify_certificate(cert, TABLES)
    finally:
        for owner, name, old in reversed(patches):
            setattr(owner, name, old)
    tests.append('15 positive controls/fixedF negatives unchanged with every template search, compiler, numeric and producer API disabled')
    result = {
        'status': 'PASS', 'python': platform.python_version(),
        'command': 'uv run --no-project python -B test_circuits.py',
        'elapsed_seconds': time.monotonic() - started,
        'scope': 'Executable constructor-witness interface and ordinary exact-calculus argument; no binary codec, TM state count or internal PA theorem',
        'all_rule_tags': list(range(12)), 'positive_controls': len(controls),
        'fixed_default_F_rejections': len(controls), 'template_identity_cases': template_cases,
        'static_circuit_steps': {str(k): len(v.steps) for k, v in TABLES.items()},
        'deep_bundle_stats': stats,
        'tests': tests, 'rejected_corruptions': rejects,
        'trusted_spec': 'source50/data/spec254.json',
        'source_sha256': {name: sha256((BASE/name).read_bytes()).hexdigest()
                          for name in ['term_circuits.py', 'test_circuits.py',
                                       'source50/data/spec254.json']},
    }
    (BASE/'circuit-results.json').write_text(json.dumps(result, indent=2) + '\n')
    (BASE/'example-circuit-bundle.json').write_text(json.dumps({
        'description': 'Positive bundle(0,1,2), not a refutation',
        'trusted_control_goal': controls[11][1], 'certificate': controls[11][0]}, indent=2)+'\n')
    (BASE/'fixed-circuits.json').write_text(json.dumps({str(k): {
        'arity': v.arity, 'steps': v.steps, 'root': v.root} for k,v in TABLES.items()}, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
