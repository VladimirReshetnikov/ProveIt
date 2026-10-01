"""Absorb native size comparisons into positive scale coordinates.

The source retains the complete coupled U9 relation. Reparametrizing
X=q*w as X=q*(r+beta) removes one supplied coordinate and comparison.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_joint_and_coupled as parent

compiler = parent.compiler
PREFIXES = parent.PREFIXES
SPECS = {
    'geo__': ('Q', 'geometry_index', 'geo__geometry_X_bound'),
    'and__': ('and__q', 'and__bs_packed', 'and__bs_X_bound'),
}
polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound


def rewrite(old, prefixes=PREFIXES):
    prefixes = tuple(prefixes)
    assert prefixes and len(set(prefixes)) == len(prefixes)
    assert set(prefixes) <= set(PREFIXES)
    assert tuple(old['coupled_native_linear']) == PREFIXES
    assert not old.get('positive_scale_prefixes')
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    consumers = lambda name: {n for n, _, a, b in old['source'] if name in (a, b)}
    inputs = old['parameters']+old['auxiliaries']
    dependencies = {n: {n} for n in inputs}
    dep = lambda v: dependencies[v] if isinstance(v, str) else set()
    for n, _, a, b in old['source']:
        dependencies[n] = dep(a) | dep(b)
    mutable = {p+s for p in prefixes for s in ('w', 'bound_beta')}
    omitted = []
    change = {}
    for p in prefixes:
        q, r, bound = SPECS[p]
        assert rows[p+'wn2'] == ('*', p+'w', q)
        assert rows[bound] == ('+', r, p+'bound_beta')
        assert consumers(p+'w') == {p+'wn2'}
        assert consumers(p+'bound_beta') == {bound}
        assert consumers(bound) == set()
        assert all(not {p+'w', p+'bound_beta'} & set(pair) for pair in old['comparisons'])
        pair = (bound, p+'wn2')
        assert old['comparisons'].count(pair) == 1
        assert [pair for pair in old['comparisons'] if bound in pair] == [pair]
        assert not mutable & (dep(q) | dep(r))
        assert p+'w' not in old.get('public_registers', {}).values()
        change[p+'wn2'] = ('*', bound, q)
        omitted.append(pair)
    source = [(n, *change[n]) if n in change else row
              for row in old['source'] for n in [row[0]]]
    auxiliaries = [n for n in old['auxiliaries'] if n not in {p+'w' for p in prefixes}]
    source = parent.parent.parent.units.sort_source(source, old['parameters']+auxiliaries)
    pairs = [pair for pair in old['comparisons'] if pair not in omitted]
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=auxiliaries,
                  witnesses=len(auxiliaries), equations=len(pairs), operations=len(source),
                  multiplications=count['M'], additions_subtractions=count['A'],
                  positive_scale_prefixes=prefixes, positive_scale_parent=old,
                  positive_scale_removed_comparisons=omitted)
    assert len(source) == old['operations']
    assert len(pairs) == old['equations']-len(prefixes)
    assert len(auxiliaries) == old['witnesses']-len(prefixes)
    compiler.check_source(packet)
    return packet


def build(form='normalized', *, merge_bound=True, prefixes=PREFIXES):
    return rewrite(parent.build(form, merge_bound=merge_bound), prefixes)


def ledger(packet):
    source, out = polynomial_source(packet)
    old_source, _ = polynomial_source(packet['positive_scale_parent'])
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    n = len(packet['positive_scale_prefixes'])
    assert len(source) == len(old_source)-3*n
    return dict(form=packet['form'], prefixes=packet['positive_scale_prefixes'],
                bound_is_program_E=packet['bound_is_program_E'],
                certificate={k: packet[k] for k in ('operations', 'multiplications',
                    'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(source), multiplications=count['M'],
                                additions_subtractions=count['A'], output=out),
                parameters=packet['parameters'], **degree_bound(packet))


def lift_to_parent(packet, values):
    env = compiler.parent.execute(packet['source'], values)
    result = dict(values)
    for p in packet['positive_scale_prefixes']:
        q, r, bound = SPECS[p]
        result[p+'w'] = env[bound]
        result[p+'bound_beta'] = env[p+'wn2']-env[r]
    return result


def project_from_parent(packet, values):
    old = packet['positive_scale_parent']
    env = compiler.parent.execute(old['source'], values)
    result = {k: v for k, v in values.items() if k not in {
        p+'w' for p in packet['positive_scale_prefixes']}}
    for p in packet['positive_scale_prefixes']:
        result[p+'bound_beta'] = values[p+'w']-env[SPECS[p][1]]
    return result


def identity_audit(packet, seed):
    rng = random.Random(seed)
    positive_lifts = 0
    for trial in range(64):
        positive = trial < 32
        choose = (lambda: rng.randrange(1, 8)) if positive else (lambda: rng.randrange(-5, 6))
        numerals = {n: choose() for n in compiler.NUMERALS}
        if positive:
            numerals.update(recoder_radix=4, repunit_divisor=7)
        literal = parent.parent.parent.constants_parent.materialize_packet(packet, numerals)
        values = {n: choose() for n in packet['parameters']+packet['auxiliaries']}
        before_values = lift_to_parent(literal, values)
        old = literal['positive_scale_parent']
        source, out = polynomial_source(literal)
        old_source, old_out = polynomial_source(old)
        env = compiler.parent.execute(source, values)
        before = compiler.parent.execute(old_source, before_values)
        changed_bounds = {SPECS[p][2] for p in packet['positive_scale_prefixes']}
        assert all(env[n] == before[n] for n, _, _, _ in packet['source'] if n not in changed_bounds)
        assert all(before[a] == before[b] for a, b in packet['positive_scale_removed_comparisons'])
        assert env[out] == before[old_out]
        assert project_from_parent(literal, before_values) == values
        if positive:
            assert min(before_values.values()) > 0
            positive_lifts += 1
    return dict(complete_source_output_identities=64, signed_cases=32,
                exact_coordinate_round_trips=64, positive_forward_lifts=positive_lifts,
                scope='Arbitrary integer source identities with finite fixed-numeral substitutions, not full positive Pell zeros.')


def inverse_positivity_audit():
    cases = negative_joint = 0
    for r in range(4, 4100, 7):
        for epsilon in (1, -1):
            shifted = r+epsilon-1
            q = 1 << shifted.bit_count()
            X = 1 << (2*shifted+1)
            assert X % q == 0
            w = X//q
            assert w >= 1 << (shifted+1)
            assert w > r and X-r > 0
            beta = w-r
            assert q*(r+beta) == X
            assert (q-1)*r+q*beta == X-r
            cases += 1
            negative_joint += epsilon < 0
    return dict(exact_population_and_shift_cases=cases, shifted_negative_sign_cases=negative_joint,
                scope='Typed scalar coordinate maps; not complete U9 or native Pell witnesses.')


def verify():
    records = []
    for interface in (False, True):
        for form in ('units', 'normalized'):
            for prefixes in (('geo__',), ('and__',), PREFIXES):
                packet = build(form, merge_bound=interface, prefixes=prefixes)
                rec = ledger(packet)
                rec['audit'] = identity_audit(packet, 291149+len(records))
                source, output = polynomial_source(packet)
                nodes = {n: (a, b) for n, _, a, b in source}
                needed = set()
                def visit(name):
                    if not isinstance(name, str) or name not in nodes or name in needed:
                        return
                    needed.add(name)
                    for operand in nodes[name]:
                        visit(operand)
                visit(output)
                assert needed == set(nodes) and len(nodes) == len(source)
                encoded = compiler.encode_source(source)
                rec.update(source=encoded, output=output, auxiliaries=packet['auxiliaries'],
                           source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())
                records.append(rec)
    default = ledger(build())
    assert default['polynomial']['operations'] == 291
    assert default['polynomial']['multiplications'] == 142
    assert default['polynomial']['additions_subtractions'] == 149
    assert default['certificate']['witnesses'] == 49
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POSITIVE_SCALE291',
                default=default, ledgers=records,
                complete_source_output_identities=768, signed_cases=384,
                inverse_positivity=inverse_positivity_audit(),
                scope='Complete ordinary-input U9 relation, with positive native scale reparametrization. '
                      'Both fixed program interfaces are retained; all degrees are conservative upper bounds. '
                      'No change to the distinct established75/87 bounds is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['default'])
