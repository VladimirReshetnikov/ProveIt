#!/usr/bin/env python3
"""Finite QA of duplicate-permitting exact C254 path certificates."""
from copy import deepcopy
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import platform
import random
import time

import term_paths as P
import canonical254 as C
import check_term254 as CT
import symbolic254 as S
import term254 as T

BASE = Path(__file__).resolve().parent

class ProducerArena(P.LookupArena):
    """Producer only: linear interning, never a verifier dependency."""
    def __init__(self):
        super().__init__([['z']], {'lookup_records': 0})
    def b(self, tag, left, right):
        if (tag, left, right) == (0, 0, 0):
            return 0
        key = ['b', tag, left, right]
        for i in range(1, len(self.nodes)):
            if self.nodes[i] == key:
                return i
        self.nodes.append(key)
        return len(self.nodes) - 1


def bundle_fixture(a_is_equal):
    a = ProducerArena()
    f = a.b(1, 0, 0)
    a.nodes.append(['b', 1, 0, 0])
    f_duplicate = len(a.nodes) - 1
    args = [f, 0, f_duplicate] if a_is_equal else [0, f, f_duplicate]
    out = a.apply('bundle', args)
    cert = {'format': P.FORMAT, 'nodes': a.nodes,
            'proof_rows': [{'tag': 11, 'args': args, 'children': [],
                            'formula': out, 'gate_paths': [[], []]}]}
    return cert, out


def main():
    started = time.monotonic()
    tests, rejected = [], []
    specimens = [S.Raw(0), S.Raw(1, (0,), (S.Raw(0), S.Raw(0))),
                 S.Raw(2, (1,), (S.Raw(0),))]
    specimens += [S.Raw(tag, tuple(range(S.ARITY[tag]))) for tag in range(3, 11)]
    specimens += [S.Raw(11, (0, 1, 2))]
    controls = []
    for raw in specimens:
        term, goal = CT.convert_control(raw)
        cert = P.from_term(term)
        stats = {}
        assert P.verify_certificate(cert, goal=goal, stats=stats)
        assert stats['arena_uniqueness_comparisons'] == 0
        assert not P.verify_certificate(cert)
        controls.append((cert, goal))
    tests.append('all12 exact source50 rule controls converted; fixedF rejects all12')

    quoted = C.make_certificate(S.Raw(2, (1,), (S.Raw(0),)), 6)
    term, goal = T.from_canonical(quoted)
    controls.append((P.from_term(term), goal))
    assert P.verify_certificate(controls[-1][0], goal=goal)
    tests.append('exact quoted canonical GEN adapter')

    gen, gen_goal = controls[2]
    duplicate = deepcopy(gen)
    duplicate['nodes'].append(deepcopy(duplicate['nodes'][1]))
    assert P.verify_certificate(duplicate, goal=gen_goal)
    old_duplicate = deepcopy(duplicate)
    old_duplicate['format'] = 'term-c254-v1'
    assert not T.verify_certificate(old_duplicate, goal=gen_goal)
    controls.append((duplicate, gen_goal))
    tests.append('unused duplicated positive key accepted; original canonical checker rejects it')

    for side in (True, False):
        cert, target = bundle_fixture(side)
        args = cert['proof_rows'][0]['args']
        assert args[2] != args[0] and args[2] != args[1]
        assert P.find_path(cert['nodes'], args[2], args[0 if side else 1]) is None
        stats = {}
        assert not P.verify_certificate(cert, goal=target, stats=stats)
        assert stats['reason'] == ('bundle_gate_1' if side else 'bundle_gate_2')
        rejected.append(stats['reason'] + '_different_IDs_equal_value')
    tests.append('both genuine exact bundle templates with pointer-distinct equal-value parameters rejected at gate')

    depth = 2048
    a = ProducerArena()
    x, y = a.b(1, 0, 0), a.b(3, 0, 0)
    for _ in range(depth):
        x, y = a.b(2, 0, x), a.b(2, 0, y)
    path = [1] * depth
    assert P.distinguish(a.nodes, x, y, path)
    assert P.find_path(a.nodes, x, y) == path
    out = a.apply('bundle', [x, 0, y])
    deep = {'format': P.FORMAT, 'nodes': a.nodes,
            'proof_rows': [{'tag': 11, 'args': [x, 0, y], 'children': [],
                            'formula': out, 'gate_paths': [path, []]}]}
    deep_stats = {}
    assert P.verify_certificate(deep, goal=out, stats=deep_stats)
    assert deep_stats['path_edges'] == depth
    assert deep_stats['arena_uniqueness_comparisons'] == 0
    controls.append((deep, out))
    tests.append('2048-edge witness and genuine deep bundle accepted without numeric materialization')
    for label, witness in [('short', path[:-1]), ('trailing', path + [0]),
                           ('bad_bit', path + [2]), ('negative_bit', [-1]),
                           ('bool_bit', [True]), ('not_list', tuple(path)),
                           ('empty_before_difference', [])]:
        assert not P.distinguish(a.nodes, x, y, witness), label
        rejected.append('path_' + label)
    eq_nodes = [['z'], ['b', 1, 0, 0], ['b', 1, 0, 0]]
    for length in range(5):
        for bits in product((0, 1), repeat=length):
            assert not P.distinguish(eq_nodes, 1, 2, list(bits))
    tests.append('all31 binary witnesses of length<=4 reject equal duplicated leaves')

    def reject(label, cert, goal):
        stats = {}
        assert not P.verify_certificate(cert, goal=goal, stats=stats), label
        rejected.append(label)
    truth = controls[0][0]
    for label, edit in [
        ('zero_alias', lambda c: c['nodes'].append(['b', 0, 0, 0])),
        ('self_reference', lambda c: c['nodes'].append(['b', 1, len(c['nodes']), 0])),
        ('bool_constructor_tag', lambda c: c['nodes'].append(['b', True, 0, 0])),
        ('negative_reference', lambda c: c['nodes'].append(['b', 1, -1, 0])),
        ('false_claimed_formula', lambda c: c['proof_rows'][0].update(formula=1)),
        ('empty_proof', lambda c: c.update(proof_rows=[])),
    ]:
        cert = deepcopy(truth); edit(cert); reject(label, cert, 0)
    cert = deepcopy(controls[1][0])
    f = len(cert['nodes']); cert['nodes'].append(['b', 1, 0, 0])
    cert['proof_rows'][-1]['args'] = [f]
    cert['proof_rows'][-1]['formula'] = f
    reject('false_MP_conclusion', cert, f)
    cert = deepcopy(controls[11][0]); del cert['proof_rows'][-1]['gate_paths']
    reject('missing_gate_paths', cert, controls[11][1])
    cert = deepcopy(gen); cert['goal'] = gen_goal
    assert not P.verify_certificate(cert)
    tests.append('certificate cannot select its own fixed default goal')

    # Independent small-denotation oracle is test-only, never called by checker.
    rng = random.Random(254)
    nodes, values, levels = [['z']], [0], [0]
    for i in range(1, 101):
        eligible = [j for j, level in enumerate(levels) if level < 3]
        left, right = rng.choice(eligible), rng.choice(eligible)
        tag = rng.randrange(4)
        if (tag, left, right) == (0, 0, 0):
            tag = 1
        nodes.append(['b', tag, left, right])
        values.append(4 * S.pair(values[left], values[right]) + tag)
        levels.append(max(levels[left], levels[right]) + 1)
    pair_checks = 0
    for left in range(len(nodes)):
        for right in range(len(nodes)):
            witness = P.find_path(nodes, left, right)
            assert (witness is not None) == (values[left] != values[right])
            if witness is not None:
                assert P.distinguish(nodes, left, right, witness)
            pair_checks += 1
    tests.append('10201 ordered node pairs agree with small numeric denotation oracle')

    # Checker remains operational with all arithmetic and producer APIs disabled.
    def prohibited(*_args, **_kwargs):
        raise AssertionError('arithmetic/producer called by path verifier')
    patches = []
    for module in (C, S):
        for name in ('pair', 'unpair', 'parse', 'build', 'verify_certificate', 'make_certificate'):
            patches.append((module, name, getattr(module, name)))
    patches += [(C, 'quote_rows', C.quote_rows), (S.Raw, 'quote', S.Raw.quote),
                (T, 'verify_certificate', T.verify_certificate),
                (T, 'from_canonical', T.from_canonical),
                (P, 'find_path', P.find_path), (P, 'from_term', P.from_term)]
    for klass in (C.CanonicalArena, S.Arena):
        for name in ('materialize', 'literal', 'intern'):
            patches.append((klass, name, getattr(klass, name)))
    try:
        for owner, name, _ in patches:
            setattr(owner, name, prohibited)
        for cert, goal in controls:
            assert P.verify_certificate(cert, goal=goal)
            assert not P.verify_certificate(cert)
    finally:
        for owner, name, old in reversed(patches):
            setattr(owner, name, old)
    tests.append('15 positive controls and fixedF negatives pass with arithmetic/producer APIs disabled')

    result = {
        'status': 'PASS', 'python': platform.python_version(),
        'command': 'uv run --no-project python -B test_paths.py',
        'elapsed_seconds': time.monotonic() - started,
        'scope': 'Finite executable QA and ordinary proof argument; no Lean proof, binary codec, enumerator, PA theorem or TM state cost',
        'source50_source_pin': 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
        'all_rule_tags': list(range(12)), 'explicit_goal_controls': len(controls),
        'fixed_default_F_rejections': len(controls), 'ordered_node_pair_checks': pair_checks,
        'deep_witness': {'edges': depth, 'nodes': len(deep['nodes']),
                         'verifier_stats': deep_stats},
        'tests': tests, 'rejected_corruptions': rejected,
        'verifier_has_global_arena_uniqueness_test': False,
        'verifier_has_template_linear_lookup': True,
        'source_sha256': {str(p.relative_to(BASE)): sha256(p.read_bytes()).hexdigest()
                          for p in [BASE/'term_paths.py', BASE/'test_paths.py',
                                    *sorted((BASE/'source50/code').glob('*.py')),
                                    BASE/'source50/data/spec254.json']},
    }
    (BASE/'results.json').write_text(json.dumps(result, indent=2) + '\n')
    (BASE/'deep-bundle-control.json').write_text(json.dumps({
        'description': 'Positive bundle control, not a refutation',
        'trusted_control_goal': out, 'certificate': deep}, separators=(',', ':')) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
