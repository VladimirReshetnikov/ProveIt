"""Positive computed repunit and output coordinates in the explicit U9 source.

Two existing comparisons become definitions. Their computed values are
positive throughout the positive domain; all remaining source is retained.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_population_bound395 as parent

compiler = parent.compiler
D = parent.D


def project(old, *, project_J=True, project_Ahat=True):
    assert old.get('population_width')
    nodes = {n: (op, a, b) for n, op, a, b in old['source']}
    aliases, removed, source = {}, [], list(old['source'])
    if project_J:
        assert 'J' in old['auxiliaries']
        assert nodes['duration_multiple'] == ('*', 'Bm1', 'duration_quotient')
        assert nodes['duration_J'][:2] == ('+', 'duration_multiple')
        assert nodes['Bm1'] == ('-', 'B', 1)
        assert ('duration_J', 'J') in old['comparisons']
        aliases['J'] = 'duration_J'
        removed.append(('duration_J', 'J'))
    if project_Ahat:
        assert 'Ahat' in old['auxiliaries']
        guards = {'congruence_left': ('+', 'Ahat', 'Q'),
                  'congruence_right': ('+', 'congruence_right0', 2),
                  'congruence_right0': ('+', 'quotient_product', 'z'),
                  'quotient_product': ('*', 'modulus', 'quotient_hat'),
                  'modulus': ('-', 'Q', 1)}
        assert all(nodes[n] == row for n, row in guards.items())
        assert not any('congruence_left' in (a, b) for _, _, a, b in source)
        assert [pair for pair in old['comparisons'] if 'congruence_left' in pair] == [
            ('congruence_left', 'congruence_right')]
        aliases['Ahat'] = 'projected_Ahat'
        removed.append(('congruence_left', 'congruence_right'))
        source = [('projected_Ahat', '-', 'congruence_right', 'Q')
                  if n == 'congruence_left' else (n, op, a, b) for n, op, a, b in source]
    get = lambda v: aliases.get(v, v)
    source = [(n, op, get(a), get(b)) for n, op, a, b in source]
    pairs = [(get(a), get(b)) for a, b in old['comparisons'] if (a, b) not in removed]
    aux = [n for n in old['auxiliaries'] if n not in aliases]
    source = parent.bound.parent.units.units.sort_source(source, old['parameters']+aux)
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=aux,
                  projected_coordinates=aliases, projection_parent=old,
                  project_J=project_J, project_Ahat=project_Ahat)
    if 'public_registers' in old:
        packet['public_registers'] = {k: get(v) for k, v in old['public_registers'].items()}
    if 'boundary_comparisons' in old:
        # The raw packet counts a literal comparison prefix. Projected unit
        # forms retain it only as historical metadata, not as a new split.
        if old['form'] == 'raw':
            boundary = old['boundary_comparisons']
            packet['boundary_comparisons'] = boundary-sum(
                old['comparisons'].index(pair) < boundary for pair in removed)
        else:
            packet['parent_boundary_comparisons'] = old['boundary_comparisons']
            packet.pop('boundary_comparisons')
    compiler.recount(packet)
    compiler.check_source(packet)
    assert packet['operations'] == old['operations']
    assert packet['equations'] == old['equations']-len(aliases)
    assert packet['witnesses'] == old['witnesses']-len(aliases)
    return packet


@lru_cache(None)
def base(form, merge_bound):
    return parent.build(form, merge_bound=merge_bound)


def build(form='normalized', *, merge_bound=True, project_J=True, project_Ahat=True):
    return project(base(form, merge_bound), project_J=project_J, project_Ahat=project_Ahat)


def degree_bound(packet):
    degree = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    d = lambda v: degree[v] if isinstance(v, str) else 0
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    overrides = {} if packet['form'] == 'raw' else {
        p+'R15': p for p in ('geo__', 'and__', 'hist__and__')}
    for n, op, a, b in packet['source']:
        degree[n] = d(a)+d(b) if op == '*' else max(d(a), d(b))
        if n in overrides:
            p = overrides[n]
            X, ac, G, aa, cc = (p+k for k in ('wn2', 'cam2', 'gam', 'R12', 'R10a'))
            expected = {p+'R15': ('-', p+'L15', p+'Ac2'),
                p+'R14': ('+', p+'D1', G), p+'D1': ('+', X, ac),
                ac: ('*', cc, aa), G: ('*', p+'ga', p+'a4m5'),
                p+'a4m5': ('+', p+'a4', 3), p+'a4': ('*', 4, aa),
                p+'A': ('+', p+'a_square', p+'a4m5'), p+'a_square': ('*', aa, aa),
                p+'c2': ('*', cc, cc), p+'Ac2': ('*', p+'A', p+'c2'),
                p+'L15': ('*', p+'R14', p+'R14')}
            assert all(rows[key] == value for key, value in expected.items())
            degree[n] = max(2*d(X), d(X)+d(ac), d(X)+d(G),
                            d(ac)+d(G), 2*d(G), d(p+'a4m5')+2*d(cc))
    raw = packet['form'] == 'raw'
    pairs = packet['comparisons'] if raw else packet['comparisons'][:-1]
    maximum = max(max(d(a), d(b)) for a, b in pairs)
    product = 0 if raw else d(packet['unit_register'])
    key = packet['project_J'], packet['project_Ahat']
    expected = {'raw': {(False, False): 544, (False, True): 544,
                        (True, False): 544, (True, True): 544},
                'units': {(False, False): 1384, (False, True): 1386,
                          (True, False): 1403, (True, True): 1405},
                'normalized': {(False, False): 2204, (False, True): 2206,
                               (True, False): 2239, (True, True): 2241}}
    assert product+2*maximum == expected[packet['form']][key]
    return dict(degree_upper_bound=product+2*maximum, unit_degree_bound=product,
                maximum_residual_degree_bound=maximum,
                native_scale_degrees=[d('Q'), d('and__q'), d('hist__and__q')],
                factor_degree_bounds={n: d(n) for n in packet.get('unit_factors', [])},
                exact_degree_claimed=False)


def ledger(packet):
    source, out = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    parent_record = parent.ledger(packet['projection_parent'])
    count = len(packet['projected_coordinates'])
    assert len(source) == parent_record['polynomial']['operations']-3*count
    assert counts['M'] == parent_record['polynomial']['multiplications']-count
    assert counts['A'] == parent_record['polynomial']['additions_subtractions']-2*count
    return dict(form=packet['form'], project_J=packet['project_J'],
        project_Ahat=packet['project_Ahat'], bound_is_program_E=packet['bound_is_program_E'],
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=out),
        parameters=packet['parameters'], **degree_bound(packet))


def verify():
    rng = random.Random(389189200)
    records, identities, signed, positive_lifts = [], 0, 0, 0
    for form in ('raw', 'units', 'normalized'):
        for merge_bound in (False, True):
            old = base(form, merge_bound)
            osource, oout = compiler.parent.polynomial_source(old)
            for project_J, project_Ahat in ((False, False), (False, True), (True, False), (True, True)):
                packet = build(form, merge_bound=merge_bound, project_J=project_J, project_Ahat=project_Ahat)
                records.append(ledger(packet))
                source, out = compiler.parent.polynomial_source(packet)
                for case in range(32):
                    positive = case < 16
                    constants = {n: rng.randrange(1, 8) if positive else rng.randrange(-5, 6)
                                 for n in compiler.NUMERALS}
                    if positive:
                        constants['recoder_radix'] = 4
                        constants['repunit_divisor'] = 7
                    values = {n: rng.randrange(1, 5) if positive else rng.randrange(-3, 4)
                              for n in packet['parameters']+packet['auxiliaries']}
                    after = compiler.parent.execute(compiler.materialize(source, constants), values)
                    restored = dict(values)
                    for name, register in packet['projected_coordinates'].items():
                        restored[name] = after[register]
                    before = compiler.parent.execute(compiler.materialize(osource, constants), restored)
                    assert after[out] == before[oout]
                    if project_J:
                        assert before['duration_J'] == restored['J']
                    if project_Ahat:
                        assert before['congruence_left'] == before['congruence_right']
                    common = {n for n, _, _, _ in source} & {n for n, _, _, _ in osource}
                    assert all(after[n] == before[n] for n in common
                               if not n.startswith(('sos_', 'history_', 'unit_')))
                    if positive:
                        assert all(v > 0 for v in restored.values())
                        if project_J:
                            assert restored['J'] >= after['B']
                            assert after['geometry_index']-after['B'] > 0
                        if project_Ahat:
                            assert restored['Ahat'] >= 2
                        positive_lifts += 1
                    identities += 1
                    signed += not positive
    packet = build()
    source, out = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(source)
    record = ledger(packet)
    assert record['polynomial']['operations'] == 389
    assert (record['polynomial']['multiplications'], record['polynomial']['additions_subtractions']) == (189, 200)
    assert record['certificate']['witnesses'] == 67
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POPULATION_PROJECTION389', ledgers=records,
                full_projected_polynomial_identities=identities, signed_cases=signed,
                positive_coordinate_lifts=positive_lifts,
                fixed_recipe=parent.parent.u9.components()[-1],
                source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                example=dict(source=encoded, output=out, comparisons=packet['comparisons'],
                             parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                             fixed_numeral_definitions=compiler.NUMERALS),
                scope='One fixed U9-derived universal polynomial costs389 operations with67 '
                      'positive witnesses and four positive program parameters; degree at most2241. '
                      'Computed J and Ahat give positive coordinate projections and exact polynomial '
                      'identities after substitution. The392-operation Ahat-only form has degree '
                      'at most2206. Huge fixed numerals remain the same exact finite recipes.')


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
    print(result['ledgers'][-1])
