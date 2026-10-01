"""Absorb the lower-output bound into a positive mask/quotient gap.

The complete positive zero set is in bijection with the selected loader288
parent. The polynomial-identity lift is positive at zeros, not on arbitrary
positive inputs; a second unconditional positive lift has a paid residual
correction recorded explicitly below.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_loader_scale288 as parent

compiler = parent.compiler
units = parent.units
execute = parent.execute
EXPECTED = [(o-3, d, w-1) for o, d, w in parent.EXPECTED]


def rewrite(old):
    assert old.get('loader_defined_scale') and not old.get('positive_mask_gap')
    compiler.check_source(old)
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    expected = {
        'input_bound': ('+', 'x', 'input_slack'),
        'joined_scale_floor': ('+', 'input_bound', 'z'),
        'load__r': ('+', 'joined_scale_floor', 'power_gap'),
        'modulus': ('*', compiler.Numeral('repunit_divisor'), 'load__r'),
        'Q': ('+', 'modulus', 1),
        'B': ('*', compiler.Numeral('recoder_radix'), 'Q'),
        'Bm1': ('-', 'B', 1),
        'twiceB': ('+', 'B', 'B'),
        'twiceBm1': ('-', 'twiceB', 1),
        'mask_product': ('*', 'twiceBm1', 'K'),
        'mask_scale': ('+', 'mask_product', 1),
        'quotient_product': ('*', 'modulus', 'quotient_hat'),
        'congruence_right0': ('+', 'quotient_product', 'z'),
        'congruence_right': ('+', 'congruence_right0', 2),
        'projected_Ahat': ('-', 'congruence_right', 'Q'),
        'fusion_output_bound': ('+', 'projected_Ahat', 'fusion_output_slack'),
        'repunit_product': ('*', 'Bm1', 'duration_J'),
        'repunit_P': ('+', 'repunit_product', 1),
        'scale': ('*', 'input_bound', 'repunit_P'),
    }
    assert all(rows[n] == row for n, row in expected.items())
    removed = ('fusion_output_bound', 'scale')
    retained = ('mask_scale', 'scale')
    assert old['comparisons'].count(removed) == old['comparisons'].count(retained) == 1
    consumers = lambda v: {n for n, _, a, b in old['source'] if v in (a, b)}
    assert consumers('fusion_output_slack') == {'fusion_output_bound'}
    assert not consumers('fusion_output_bound')
    assert all(pair == removed for pair in old['comparisons'] if 'fusion_output_bound' in pair)
    assert all('fusion_output_slack' not in pair for pair in old['comparisons'])
    assert 'K' in old['auxiliaries'] and 'K' not in old['parameters']
    assert 'fusion_output_slack' in old['auxiliaries']
    def leaves(v):
        if isinstance(v, str): return {v}
        if isinstance(v, dict): v = v.values()
        elif not isinstance(v, (list, tuple)): return set()
        return set().union(*(leaves(a) for a in v))
    assert not {'fusion_output_bound', 'fusion_output_slack'} & leaves(old.get('public_registers', {}))
    assert not {'fusion_output_bound', 'fusion_output_slack'} & leaves(old.get('interfaces', {}))
    source = [row for row in old['source'] if row[0] != 'fusion_output_bound']
    source.append(('K', '+', 'quotient_hat', 'fusion_output_slack'))
    auxiliaries = [n for n in old['auxiliaries'] if n != 'K']
    source = parent.sort_source(source, old['parameters']+auxiliaries)
    pairs = [p for p in old['comparisons'] if p != removed]
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=auxiliaries,
        operations=len(source), multiplications=count['M'], additions_subtractions=count['A'],
        equations=len(pairs), witnesses=len(auxiliaries), positive_mask_gap=True,
        mask_gap_parent=old, mask_gap_removed_comparison=removed,
        mask_gap_retained_scale_comparison=retained,
        mask_gap_identity_lift_positive_only_at_zeros=True)
    assert count == Counter('M' if op == '*' else 'A' for _, op, _, _ in old['source'])
    assert packet['equations'] == old['equations']-1
    assert packet['witnesses'] == old['witnesses']-1
    compiler.check_source(packet)
    return packet


def build(operations=285, *, merge_bound=True, witnesses=None):
    assert witnesses in (None, 47, 48, 49)
    return rewrite(parent.build(operations+3, merge_bound=merge_bound,
        witnesses=None if witnesses is None else witnesses+1))


polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound


def ledger(packet):
    source, output = polynomial_source(packet)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    old = packet['mask_gap_parent']
    assert degree_bound(packet) == degree_bound(old)
    return dict(certificate={n: packet[n] for n in ('operations', 'multiplications',
        'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=count['M'],
            additions_subtractions=count['A'],
            degree_upper_bound=degree_bound(packet)['degree_upper_bound'], exact_degree_claimed=False),
        bound_is_program_E=packet['bound_is_program_E'], parameters=packet['parameters'],
        factor_partition=packet['factor_partition'], partition_anchor=packet['partition_anchor'],
        output=output)


def lift_to_parent(packet, values, *, positive_extension=False):
    env = execute(packet['source'], values)
    boundary = env['mask_scale'] if positive_extension else env['scale']
    return dict(values, K=env['K'], fusion_output_slack=boundary-env['projected_Ahat'])


def project_from_parent(packet, values):
    result = {n: v for n, v in values.items() if n != 'K'}
    result['fusion_output_slack'] = values['K']-values['quotient_hat']
    return result


def audit(packet, seed):
    rng = random.Random(seed)
    old_source, old_output = polynomial_source(packet['mask_gap_parent'])
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
        assert all(env[n] == before[n] for n, _, _, _ in packet['mask_gap_parent']['source']
                   if n != 'fusion_output_bound')
        assert before['fusion_output_bound'] == before['scale']
        assert env[output] == before[old_output]
        assert project_from_parent(literal, restored) == values
        positive_restored = lift_to_parent(literal, values, positive_extension=True)
        alternative = execute(compiler.materialize(old_source, numerals), positive_restored)
        residual = env['mask_scale']-env['scale']
        assert alternative['fusion_output_bound']-alternative['scale'] == residual
        weight = env[packet['unit_register']] if packet['unit_product'] else 1
        assert alternative[old_output] == env[output]+weight*residual*residual
        assert project_from_parent(literal, positive_restored) == values
        if positive:
            assert min(positive_restored.values()) > 0
    return dict(whole_output_identities=32, signed_cases=16,
        corrected_positive_extension_identities=32, unconditional_positive_extensions=16,
        coordinate_round_trips=64)


def typed_audit():
    cases = padded = 0
    for D in (2, 3, 4, 7):
      for n in (2, 4, 8, 16):
        q = 1 << n; Q = q**D; B = (1 << (D-1))*Q
        J = (B**n-1)//(B-1)
        scale = q*B**n
        assert (scale-1) % (2*B-1) == 0
        K = (scale-1)//(2*B-1)
        for x in list(range(1, min(q, 65)))+[q-1]:
            z = sum(((x >> i)&1)*(1 << (D*i)) for i in range(n))
            A = (x*J)&K
            assert (A-z) % (Q-1) == 0 and A >= z
            h = (A-z)//(Q-1)+1
            assert K > J >= h >= 1 and (q+1)*(h-1) <= J
            assert 3*K > q*J
            slack = scale-A-1
            assert slack > 0 and (Q-1)*(h-1)+z+1 == A+1
            cases += 1
            repunit = (Q-1)//((1 << D)-1)
            padded += repunit-q-z > 0
    # The identity lift is intentionally not declared positive off zeros.
    # These are finite substituted outer coordinates, not native zeros.
    q,z,b,h,g,duration_bound,duration_quotient = 2,1,1,100,1,2,1
    Q = 7*(q+z+b)+1; B = 4*Q; J = (B-1)*duration_quotient+duration_bound
    K = h+g; Ahat = (Q-1)*(h-1)+z+1
    scale = q*((B-1)*J+1); mask = (2*B-1)*K+1
    # Make the quotient large enough to exceed the unrelated off-zero scale.
    h = scale+1; K = h+g; Ahat = (Q-1)*(h-1)+z+1
    mask = (2*B-1)*K+1
    assert scale-Ahat < 0 and mask-Ahat > 0 and mask != scale
    return dict(typed_recoder_cases=cases,also_admitting_positive_loader_gap=padded,
        offzero_identity_lift_counterexample=dict(q=q,z=z,Q=Q,B=B,J=J,
            quotient_hat=h,K=K,scale=scale,mask_scale=mask,Ahat=Ahat,
            identity_slack=scale-Ahat,unconditional_slack=mask-Ahat),
        scope='Exact typed recoder values and an off-zero regression; no full native Pell zeros.')


def verify():
    records = []
    for interface in (False, True):
      for operations, degree, witnesses in EXPECTED:
        packet = build(operations, merge_bound=interface)
        rec = ledger(packet)
        assert rec['polynomial']['operations'] == operations
        assert rec['polynomial']['degree_upper_bound'] == degree
        assert packet['witnesses'] == witnesses
        rec['audit'] = audit(packet, 285295+len(records))
        source, output = polynomial_source(packet)
        parent.source_closure(source, output)
        encoded = compiler.encode_source(source)
        rec.update(source=encoded, auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest())
        records.append(rec)
    restricted = []
    for interface in (False, True):
        packet = build(292, merge_bound=interface, witnesses=47)
        rec = ledger(packet)
        assert rec['polynomial']['degree_upper_bound'] == 1344
        rec['audit'] = audit(packet, 285477+interface)
        source, output = polynomial_source(packet)
        parent.source_closure(source, output)
        rec.update(source=compiler.encode_source(source), auxiliaries=packet['auxiliaries'])
        restricted.append(rec)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_MASK_GAP285',frontier=EXPECTED,
        ledgers=records,fixed47_degree1344=restricted,
        whole_output_identities=32*(len(records)+len(restricted)),
        signed_cases=16*(len(records)+len(restricted)),
        corrected_positive_extension_identities=32*(len(records)+len(restricted)),
        typed_recoder_audit=typed_audit(),
        scope='Positive zero-set bijection with the selected loader288 parent. '
              'Universal ordinary-input theorem on valid U9 slices is inherited; '
              'unconditional positive lift has an explicit scale-residual correction. '
              'All degree claims are upper bounds and separate75/87 are unchanged.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=json.loads(json.dumps(verify()))
    path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert result==json.loads(path.read_text()),'receipt mismatch'
    print(result['status']);print(result['frontier']);print(result['typed_recoder_audit'])
