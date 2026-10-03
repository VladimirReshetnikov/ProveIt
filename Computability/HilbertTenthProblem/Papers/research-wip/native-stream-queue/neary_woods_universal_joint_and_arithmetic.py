"""Two sign-recovered native index units in the complete joint-AND source."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_joint_and_units as parent
import group_projective_index_unit as index_reference

compiler = parent.compiler
PREFIXES = parent.PREFIXES
polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound


def rewrite(old, prefixes=PREFIXES):
    prefixes = tuple(prefixes)
    assert prefixes and len(set(prefixes)) == len(prefixes)
    assert all(p in PREFIXES for p in prefixes)
    assert old['form'] in ('units', 'normalized') and old['joint_native_and']
    assert tuple(old['core_prefixes']) == PREFIXES
    assert not old.get('merged_native_indices')
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    fixed = compiler.Numeral
    critical = {
        'input_bound': ('+', 'x', 'input_slack'),
        'joined_scale_floor': ('+', 'input_bound', 'z'),
        'Q': ('+', 'joined_scale_floor', 'power_gap'),
        'B': ('*', fixed('recoder_radix'), 'Q'),
        'Bm1': ('-', 'B', 1),
        'duration_multiple': ('*', 'Bm1', 'duration_quotient'),
        'duration_J': ('+', 'duration_multiple', 'program_duration_bound'),
        'geometry_index': ('*', fixed('repunit_divisor'), 'duration_J'),
        'geo__geometry_even': ('*', 2, 'geo__odd_half'),
        'geo__geometry_odd': ('+', 'geo__geometry_even', 1),
        'geo__geometry_X_bound': ('+', 'geometry_index', 'geo__bound_beta'),
        'and__bs_X_bound': ('+', 'and__bs_packed', 'and__bound_beta'),
        'and__bs_p0': ('*', 'and__q', 'and__F3'),
        'and__bs_p1': ('+', 'and__F2', 'and__bs_p0'),
        'and__bs_p2': ('*', 'and__q', 'and__bs_p1'),
        'and__bs_p3': ('+', 'and__F1', 'and__bs_p2'),
        'and__bs_p4': ('*', 'and__q', 'and__bs_p3'),
        'and__bs_packed': ('+', 'and__F0', 'and__bs_p4'),
        'and__shared_sum02': ('+', 'and__F0', 'and__F2'),
        'and__input_A': ('+', 'and__F1', 'and__F3'),
        'and__bs_Q': ('+', 'and__shared_sum02', 'and__input_A'),
        'and__bs_q': ('-', 'and__q', 'and__bs_Q'),
    }
    assert all(rows[n] == row for n, row in critical.items())
    assert ('geo__geometry_X_bound', 'geo__wn2') in old['comparisons']
    assert ('and__bs_X_bound', 'and__wn2') in old['comparisons']
    assert old['unit_factors'].count('and__bs_q') == 1
    assert old['comparisons'][-1] == (old['unit_register'], 1)
    r_registers = {'geo__': 'geometry_index', 'and__': 'and__bs_packed'}
    scales = {'geo__': 'Q', 'and__': 'and__q'}
    odds = {'geo__': 'geo__geometry_odd', 'and__': 'and__bs_odd'}
    for p in PREFIXES:
        local = {
            p+'wn2': ('*', p+'w', scales[p]),
            p+'sn2': ('*', odds[p], scales[p]),
            p+'UM': ('*', p+'wn2', p+'sn2'),
            p+'R10b': ('+', p+'eta', p+'zeta'),
            p+'ksn2': ('*', p+'R10b', p+'sn2'),
            p+'R10a': ('+', p+'ksn2', p+'eta'),
            p+'R12': ('+', p+'UM', p+'sn2'),
            p+'hpm1': ('*', p+'h', p+'UM'),
            p+'r1': ('+', r_registers[p], 1),
            p+'tr1': ('+', p+'r1', r_registers[p]),
            p+'R11': ('+', p+'r1', p+'hpm1'),
            p+'H17': ('-', p+'jc', p+'tr1'),
            p+'aux_u_rhs': ('-', p+'of', p+'R10a'),
        }
        assert all(rows[n] == row for n, row in local.items())
        assert (p+'H17', p+'aux_u_rhs') in old['comparisons']
    removed = [(p+'R10b', p+'R11') for p in prefixes]
    assert all(pair in old['comparisons'] for pair in removed)
    changed = {p+'R11': p for p in prefixes}
    for name in changed:
        assert not any(name in (a, b) for _, _, a, b in old['source'])
        assert [pair for pair in old['comparisons'] if name in pair] == [
            (changed[name]+'R10b', name)]
        assert name not in old.get('public_registers', {}).values()
    source = [(n, '-', changed[n]+'R10b', changed[n]+'hpm1') if n in changed else row
              for row in old['source'] for n in [row[0]]]
    unit = old['unit_register']
    added = []
    for p in prefixes:
        factor, nxt = p+'index_unit', p+'index_all_units'
        assert factor not in rows and nxt not in rows
        source += [(factor, '-', p+'R11', r_registers[p]),
                   (nxt, '*', unit, factor)]
        added.append(factor)
        unit = nxt
    pairs = [pair for pair in old['comparisons'][:-1] if pair not in removed]+[(unit, 1)]
    source = parent.units.sort_source(source, old['parameters']+old['auxiliaries'])
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=pairs,
                  operations=len(source), equations=len(pairs),
                  multiplications=cc['M'], additions_subtractions=cc['A'],
                  unit_register=unit, unit_factors=old['unit_factors']+added,
                  merged_native_indices=prefixes, index_parent=old,
                  index_parent_comparisons=removed, index_r_registers=r_registers)
    assert len(source) == old['operations']+2*len(prefixes)
    assert len(pairs) == old['equations']-len(prefixes)
    assert packet['auxiliaries'] == old['auxiliaries']
    compiler.check_source(packet)
    return packet


def build(form='normalized', *, merge_bound=True, prefixes=PREFIXES):
    return rewrite(parent.build(form, merge_bound=merge_bound), prefixes)


def ledger(packet):
    source, out = polynomial_source(packet)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    old = packet['index_parent']
    old_source, _ = polynomial_source(old)
    n = len(packet['merged_native_indices'])
    old_cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in old_source)
    assert len(source) == len(old_source)-n
    assert cc['M'] == old_cc['M'] and cc['A'] == old_cc['A']-n
    degree = degree_bound(packet)
    addition = sum(5 if p == 'geo__' else 185 for p in packet['merged_native_indices'])
    assert degree['degree_upper_bound'] == parent.degree_bound(old)['degree_upper_bound']+addition
    return dict(form=packet['form'], prefixes=list(packet['merged_native_indices']),
                bound_is_program_E=packet['bound_is_program_E'],
                certificate={k: packet[k] for k in ('operations', 'multiplications',
                    'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(source), multiplications=cc['M'],
                                additions_subtractions=cc['A'], output=out),
                parameters=packet['parameters'], **degree)


def audit_identity(packet, values):
    old = packet['index_parent']
    source, out = polynomial_source(packet)
    old_source, old_out = polynomial_source(old)
    execute, scalar = compiler.parent.execute, compiler.parent.scalar
    env, before = execute(source, values), execute(old_source, values)
    changed = {p+'R11' for p in packet['merged_native_indices']}
    assert all(env[n] == before[n] for n, _, _, _ in old['source'] if n not in changed)
    rr = []
    for p in packet['merged_native_indices']:
        r = before[p+'R10b']-before[p+'R11']
        assert env[p+'index_unit'] == r+1
        assert env[p+'index_unit'] == env[p+'R10b']-env[p+'hpm1']-env[packet['index_r_registers'][p]]
        rr.append(r)
    removed = set(packet['index_parent_comparisons'])
    residuals = [scalar(a, before)-scalar(b, before) for a, b in old['comparisons'][:-1]
                 if (a, b) not in removed]
    assert residuals == [scalar(a, env)-scalar(b, env) for a, b in packet['comparisons'][:-1]]
    unit, factor = before[old['unit_register']], 1
    for r in rr:
        factor *= 1+r
    outer = 1+sum(r*r for r in residuals)
    assert env[packet['unit_register']] == unit*factor
    assert env[out] == unit*factor*outer-1
    assert env[out]-before[old_out] == unit*((factor-1)*outer-sum(r*r for r in rr))
    return True


def geometry_bounds():
    cases = 0
    for width in (3, 4, 8, 15):
      for q in (2, 3, 7, 16):
       for z in (1, 2, 5):
        for gap in (1, 4):
         for odd_half in (1, 3):
          Q = q+z+gap
          B = (1 << (width-1))*Q
          ell = 2
          J = (B-1)+ell
          r = ((1 << width)-1)*J
          X = Q*(r//Q+1)
          Y = (2*odd_half+1)*Q
          E, a = X*Y, Y*(X+1)
          assert Q >= 4 and Y >= 12 and r >= 112
          assert X > r and E > 2*r+1 and a > 2*r+1
          assert Y*(r-1) > 2*(2*r+1)
          assert 0 < r-1 < r+1 < E
          A = a+2
          assert 2*X*Y*Y+1 > A and A**6 > A*(A*A-1)**2
          cases += 1
    return cases


def malformed_contracts():
    p = parent.build()
    cases = 0
    for name, replacement in (
        ('geo__R11', ('+', 'geo__r1', 1)),
        ('geometry_index', ('*', 1, 'duration_J')),
        ('Q', ('+', 'input_bound', 'power_gap')),
        ('and__bs_packed', ('+', 'and__F1', 'and__bs_p4')),
    ):
        bad = dict(p, source=[(n, *replacement) if n == name else row
                              for row in p['source'] for n in [row[0]]])
        try:
            rewrite(bad)
        except AssertionError:
            cases += 1
        else:
            raise AssertionError('malformed contract accepted')
    bad = dict(p, source=p['source']+[('bad_external', '+', 'geo__R11', 1)])
    try:
        rewrite(bad)
    except AssertionError:
        cases += 1
    else:
        raise AssertionError('external private consumer accepted')
    return cases


def verify():
    rng = random.Random(301144157)
    records, cases, signed = [], 0, 0
    for merge_bound in (False, True):
      for form in ('units', 'normalized'):
       for prefixes in (('geo__',), ('and__',), PREFIXES):
        packet = build(form, merge_bound=merge_bound, prefixes=prefixes)
        records.append(ledger(packet))
        for case in range(64):
            positive = case < 32
            C = {n: rng.randrange(1, 8) if positive else rng.randrange(-5, 6)
                 for n in compiler.NUMERALS}
            if positive:
                C['recoder_radix'], C['repunit_divisor'] = 4, 7
            literal = parent.constants_parent.materialize_packet(packet, C)
            values = {n: rng.randrange(1, 5) if positive else rng.randrange(-3, 4)
                      for n in packet['parameters']+packet['auxiliaries']}
            audit_identity(literal, values)
            cases += 1
            signed += not positive
    packet = build()
    source, out = polynomial_source(packet)
    encoded = compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_JOINT_AND_ARITHMETIC',
                ledgers=records, complete_parent_output_corrections=cases, signed_cases=signed,
                geometry_bootstrap_fixtures=geometry_bounds(),
                joint_weak_checksum=index_reference.weak_checksum_checks(),
                exact_pell_doubling=index_reference.duplication_checks(),
                malformed_contract_rejections=malformed_contracts(),
                source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                example=dict(source=encoded, output=out, comparisons=packet['comparisons'],
                    parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                    fixed_numeral_definitions=compiler.NUMERALS),
                scope='Both native first-index comparisons join the existing safe unit product. '
                      'Each index sign is restored before typing using the retained full strong '
                      'equation, X>r and both ratio slacks. Same positive supplied tuples and '
                      'positive zero sets as the303 parent; the off-zero polynomial changes. '
                      'Default301=144M157A,51 witnesses,14 comparisons, degree at most2475.')


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
