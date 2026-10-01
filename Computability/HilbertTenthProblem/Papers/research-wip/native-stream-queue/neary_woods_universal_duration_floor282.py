"""Make the input scale exceed its duration and remove the duration bound.

The positive forward lift is unconditional. Completeness retains the
parent's valid-program leading-zero padding scope; this is not a
bijection of all supplied parent zeros.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_mask_gap285 as parent

compiler = parent.compiler
units = parent.units
execute = parent.execute
EXPECTED = [(o-3, d, w-1) for o, d, w in parent.EXPECTED]


def rewrite(old):
    assert old.get('positive_mask_gap') and not old.get('duration_input_floor')
    compiler.check_source(old)
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    assert 'duration_input_floor' not in rows
    expected = {
        'program_duration_bound': ('+', 'program_E' if old['bound_is_program_E']
                                   else 'program_bound', 'program_duration_gap'),
        'input_bound': ('+', 'x', 'input_slack'),
        'duration_bound': ('+', 'program_duration_bound', 'duration_slack'),
        'joined_scale_floor': ('+', 'input_bound', 'z'),
        'load__r': ('+', 'joined_scale_floor', 'power_gap'),
        'modulus': ('*', compiler.Numeral('repunit_divisor'), 'load__r'),
        'Q': ('+', 'modulus', 1),
        'B': ('*', compiler.Numeral('recoder_radix'), 'Q'),
        'Bm1': ('-', 'B', 1),
        'duration_multiple': ('*', 'Bm1', 'duration_quotient'),
        'duration_J': ('+', 'duration_multiple', 'program_duration_bound'),
    }
    assert all(rows[n] == row for n, row in expected.items())
    removed = ('duration_bound', 'Bm1')
    assert old['comparisons'].count(removed) == 1
    consumers = lambda v: {n for n, _, a, b in old['source'] if v in (a, b)}
    assert consumers('input_slack') == {'input_bound'}
    assert consumers('duration_slack') == {'duration_bound'}
    assert not consumers('duration_bound')
    assert all(pair == removed for pair in old['comparisons'] if 'duration_bound' in pair)
    assert not any({'duration_slack', 'input_slack'} & set(pair)
                   for pair in old['comparisons'])
    assert {'duration_slack', 'input_slack'} <= set(old['auxiliaries'])
    assert not {'duration_slack', 'input_slack'} & set(old['parameters'])
    def leaves(v):
        if isinstance(v, str): return {v}
        if isinstance(v, dict): v = v.values()
        elif not isinstance(v, (list, tuple)): return set()
        return set().union(*(leaves(a) for a in v))
    private = {'duration_bound', 'duration_slack', 'input_slack'}
    assert not private & leaves(old.get('public_registers', {}))
    assert not private & leaves(old.get('interfaces', {}))
    auxiliaries = [n for n in old['auxiliaries'] if n != 'duration_slack']
    source = [row for row in old['source'] if row[0] not in ('input_bound', 'duration_bound')]
    source += [('duration_input_floor', '+', 'x', 'program_duration_bound'),
               ('input_bound', '+', 'duration_input_floor', 'input_slack')]
    source = parent.parent.sort_source(source, old['parameters']+auxiliaries)
    pairs = [p for p in old['comparisons'] if p != removed]
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=auxiliaries,
        operations=len(source), multiplications=count['M'], additions_subtractions=count['A'],
        equations=len(pairs), witnesses=len(auxiliaries), duration_input_floor=True,
        duration_floor_parent=old, duration_floor_removed_comparison=removed,
        duration_floor_completeness_scope='Valid program slices with sufficiently long dyadic leading-zero padding.')
    assert count == Counter('M' if op == '*' else 'A' for _, op, _, _ in old['source'])
    assert packet['equations'] == old['equations']-1
    assert packet['witnesses'] == old['witnesses']-1
    compiler.check_source(packet)
    return packet


def build(operations=282, *, merge_bound=True, witnesses=None):
    assert witnesses in (None, 46, 47, 48)
    return rewrite(parent.build(operations+3, merge_bound=merge_bound,
        witnesses=None if witnesses is None else witnesses+1))


polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound


def ledger(packet):
    source, output = polynomial_source(packet)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert degree_bound(packet) == degree_bound(packet['duration_floor_parent'])
    return dict(certificate={n: packet[n] for n in ('operations', 'multiplications',
        'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=count['M'],
            additions_subtractions=count['A'],
            degree_upper_bound=degree_bound(packet)['degree_upper_bound'], exact_degree_claimed=False),
        bound_is_program_E=packet['bound_is_program_E'], parameters=packet['parameters'],
        factor_partition=packet['factor_partition'], partition_anchor=packet['partition_anchor'],
        output=output)


def lift_to_parent(packet, values):
    env = execute(packet['source'], values)
    ell = env['program_duration_bound']
    return dict(values, input_slack=ell+values['input_slack'],
                duration_slack=env['Bm1']-ell)


def project_from_parent(packet, values):
    old = packet['duration_floor_parent']
    env = execute(old['source'], values)
    result = {n: v for n, v in values.items() if n != 'duration_slack'}
    result['input_slack'] = values['input_slack']-env['program_duration_bound']
    return result


def audit(packet, seed):
    rng = random.Random(seed)
    old_source, old_output = polynomial_source(packet['duration_floor_parent'])
    for case in range(32):
        positive = case < 16
        draw = lambda: rng.randrange(1, 7) if positive else rng.randrange(-4, 5)
        numerals = {n: draw() for n in compiler.NUMERALS}
        if positive: numerals.update(recoder_radix=4, repunit_divisor=7)
        literal = units.constants_parent.materialize_packet(packet, numerals)
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        source, output = polynomial_source(literal)
        env = execute(source, values)
        restored = lift_to_parent(literal, values)
        before = execute(compiler.materialize(old_source, numerals), restored)
        assert all(env[n] == before[n] for n, _, _, _ in packet['duration_floor_parent']['source']
                   if n != 'duration_bound')
        assert before['duration_bound'] == before['Bm1']
        assert env[output] == before[old_output]
        assert project_from_parent(literal, restored) == values
        if positive:
            assert min(restored.values()) > 0
            assert env['B'] >= env['Q'] > env['input_bound'] > env['program_duration_bound']
    return dict(whole_output_identities=32, signed_cases=16,
                unconditional_positive_lifts=16, coordinate_round_trips=32)


def padding_audit():
    cases = 0
    for D in (2, 3, 4, 8):
      for n in (4, 8, 16):
        radix = 1 << D
        q, Q = 1 << n, 1 << (D*n)
        B = (1 << (D-1))*Q
        J = (B**n-1)//(B-1)
        r = (Q-1)//(radix-1)
        for x in list(range(1, min(1 << (n-1), 65)))+[(1 << (n-1))-1]:
            z = sum(((x >> i)&1)*radix**i for i in range(n))
            assert r-q-z > 0 and q-x-n > 0
            assert B-1-n > 0 and (J-n) % (B-1) == 0 and (J-n)//(B-1) > 0
            assert x+n+(q-x-n) == q and (radix-1)*(q+z+(r-q-z))+1 == Q
            cases += 1
    # Typed recoder/loader coordinates may fail the new inverse.
    D, n, x = 8, 8, 251
    q, Q = 1 << n, 1 << (D*n)
    z = sum(((x >> i)&1)*(1 << (D*i)) for i in range(n))
    r = (Q-1)//((1 << D)-1)
    assert r-q-z > 0 and q-x > 0 and q-x-n == -3
    return dict(typed_padded_cases=cases,
        nonpositive_inverse_example=dict(D=D,n=n,x=x,q=q,Q=Q,z=z,r=r,
            loader_gap=r-q-z,parent_input_slack=q-x,new_input_slack=q-x-n),
        scope='Exact recoder/loader coordinates and padding inequalities, not full native Pell zeros.')


def verify():
    records = []
    for interface in (False, True):
      for operations, degree, witnesses in EXPECTED:
        packet = build(operations, merge_bound=interface)
        rec = ledger(packet)
        assert rec['polynomial']['operations'] == operations
        assert rec['polynomial']['degree_upper_bound'] == degree
        assert packet['witnesses'] == witnesses
        rec['audit'] = audit(packet, 282292+len(records))
        source, output = polynomial_source(packet)
        parent.parent.source_closure(source, output)
        encoded = compiler.encode_source(source)
        rec.update(source=encoded, auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())
        records.append(rec)
    restricted = []
    for interface in (False, True):
        packet = build(289, merge_bound=interface, witnesses=46)
        rec = ledger(packet)
        assert rec['polynomial']['degree_upper_bound'] == 1344
        rec['audit'] = audit(packet, 282466+interface)
        source, output = polynomial_source(packet)
        parent.parent.source_closure(source, output)
        rec.update(source=compiler.encode_source(source), auxiliaries=packet['auxiliaries'])
        restricted.append(rec)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_DURATION_FLOOR282',frontier=EXPECTED,
        ledgers=records,fixed46_degree1344=restricted, padding=padding_audit(),
        scope='Complete universal polynomial on inherited valid program slices; sound positive lift and padding converse. No all-parent-zero bijection.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    target = Path(__file__).with_suffix('.json')
    if args.write:
        target.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(target.read_text()) == json.loads(json.dumps(result))
    print(result['status'])
    print(result['frontier'])
    print(result['scope'])
