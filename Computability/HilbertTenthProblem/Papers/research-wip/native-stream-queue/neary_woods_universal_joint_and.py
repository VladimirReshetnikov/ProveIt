"""Concatenate the recoder and selected-history words in one complete AND.

This raw certificate replaces two existential native extensions by one.
It is not an off-zero polynomial identity or a native-witness bijection.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_population377 as parent
import native_binary_input_dilation_unit179 as ordering
import native_binary_masked_selection63 as native

compiler = parent.compiler
HISTORY_PREFIX = 'hist__and__'
LOW_NAMES = {'and__q': 'fusion_low_q',
             'and__padded_A': 'fusion_low_padded_A',
             'and__padded_B': 'fusion_low_padded_B',
             'and__F3': 'fusion_low_F3'}
SLACK = 'fusion_output_slack'


def rewrite(old):
    """Fuse the guarded raw377 interface, preserving its actual fixed table."""
    assert old['form'] == 'raw' and not old.get('joint_native_and')
    assert old['project_J'] and old['project_Ahat']
    assert old['joined_Q_bounds'] and old['shared_history_arithmetic']
    assert old['population_bound_removed']
    hp = old['history_packet']
    assert hp['scale_exponent'] == 11 and hp['selected_products'] == 3
    assert hp['tiles'] == 4 and hp['operations'] == 154
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    assert len(rows) == len(old['source'])
    expected = {
        'scale': ('*', 'q', 'P'), 'joint16B': ('*', 16, 'B'),
        'and__q': ('*', 'joint16B', 'scale'),
        'and__scaled_A': ('*', 'joint16B', 'copies'),
        'joint_A_sum': ('+', 'and__scaled_A', 'joint16duration'),
        'and__padded_A': ('+', 'joint_A_sum', 12),
        'and__scaled_B': ('*', 'joint16B', 'K'),
        'joint_B_sum': ('+', 'and__scaled_B', 'joint16duration'),
        'and__padded_B': ('-', 'joint_B_sum', 6),
        'and__scaled_Z': ('*', 'joint16B', 'projected_Ahat'),
        'joint_Z_difference': ('-', 'and__scaled_Z', 'joint16B'),
        'and__F3': ('+', 'joint_Z_difference', 8),
        'copies': ('*', 'x', 'duration_J'),
        'projected_Ahat': ('-', 'congruence_right', 'Q'),
        'congruence_right': ('+', 'congruence_right0', 2),
        'congruence_right0': ('+', 'quotient_product', 'z'),
        'quotient_product': ('*', 'modulus', 'quotient_hat'),
        'modulus': ('-', 'Q', 1),
    }
    for name, row in expected.items():
        assert rows[name] == row, name
    duration = rows['duration_J'][2]
    assert rows['duration_J'] == ('+', 'duration_multiple', duration)
    assert rows['duration_multiple'] == ('*', 'Bm1', 'duration_quotient')
    assert rows['joint16duration'] == ('*', 16, duration)
    assert rows['duration_bound'] == ('+', duration, 'duration_slack')
    assert ('duration_bound', 'Bm1') in old['comparisons']
    assert old['projected_coordinates'] == {'J': 'duration_J', 'Ahat': 'projected_Ahat'}
    for pair in [('repunit_P', 'P'), ('mask_scale', 'scale'), ('input_bound', 'q')]:
        assert pair in old['comparisons']
    H, M, Z, T = ('hist__'+hp['interfaces'][key] for key in ('H', 'M', 'Z', 'scale'))
    # The deleted core is exactly the historical standalone history core,
    # including its four input ports, every comparison and all22 auxiliaries.
    deleted = {n for n in rows if n.startswith(HISTORY_PREFIX)}
    expected_core = {'hist__'+n: (op, 'hist__'+a if isinstance(a, str) else a,
                                       'hist__'+b if isinstance(b, str) else b)
                     for n, op, a, b in hp['source'] if n.startswith('and__')}
    assert {n: rows[n] for n in deleted} == expected_core
    assert len(deleted) == 64
    removed_aux = [n for n in old['auxiliaries'] if n.startswith(HISTORY_PREFIX)]
    assert set(removed_aux) == {'hist__'+n for n in hp['auxiliaries'] if n.startswith('and__')}
    assert len(removed_aux) == 22
    private = deleted | set(removed_aux)
    removed_pairs = [p for p in old['comparisons'] if any(v in private for v in p)]
    expected_pairs = [('hist__'+a if isinstance(a, str) else a,
                       'hist__'+b if isinstance(b, str) else b)
                      for a, b in hp['comparisons'] if any(isinstance(v, str) and v.startswith('and__') for v in (a,b))]
    assert removed_pairs == expected_pairs and len(removed_pairs) == 16
    assert all(a in private and b in private for a,b in removed_pairs)
    for n, _, a, b in old['source']:
        assert n in deleted or not any(v in private for v in (a, b)), n
    # The four old port values have no outer consumer. Keeping their names
    # for the new values must alter only the surviving native component.
    for port in LOW_NAMES:
        assert all(n.startswith('and__') for n, _, a, b in old['source'] if port in (a,b))
        assert all(all(isinstance(v,str) and v.startswith('and__') for v in pair)
                   for pair in old['comparisons'] if port in pair)
    exports = set(old.get('interfaces', {}).values()) | set(old.get('public_registers', {}).values())
    assert not exports & (private | set(LOW_NAMES))
    assert not (set(LOW_NAMES.values()) | {SLACK, 'fusion_output_bound'}) & (set(rows) | set(old['auxiliaries']))
    source = [(LOW_NAMES.get(n, n), op, a, b) for n, op, a, b in old['source'] if n not in deleted]
    # Rename only the four definition sites. All existing consumers now see
    # the new concatenated values under their original public register names.
    source += [
        ('and__q', '*', 'fusion_low_q', T),
        ('fusion_high_A', '*', 'fusion_low_q', H),
        ('and__padded_A', '+', 'fusion_low_padded_A', 'fusion_high_A'),
        ('fusion_high_B', '*', 'fusion_low_q', M),
        ('and__padded_B', '+', 'fusion_low_padded_B', 'fusion_high_B'),
        ('fusion_high_Z', '*', 'fusion_low_q', Z),
        ('and__F3', '+', 'fusion_low_F3', 'fusion_high_Z'),
        ('fusion_output_bound', '+', 'projected_Ahat', SLACK),
    ]
    aux = [n for n in old['auxiliaries'] if n not in private]+[SLACK]
    source = ordering.sort_source(source, old['parameters']+aux)
    pairs = [p for p in old['comparisons'] if p not in removed_pairs]+[('fusion_output_bound', 'scale')]
    packet = dict(old, source=source, comparisons=pairs, auxiliaries=aux,
                  joint_native_and=True, fusion_parent=old,
                  native_prefixes=['geo__', 'and__'],
                  historical_history_packet=hp,
                  history_core_embedded=False,
                  fusion_removed_registers=sorted(deleted),
                  fusion_removed_auxiliaries=removed_aux,
                  fusion_removed_comparisons=removed_pairs,
                  fusion_interfaces=dict(low_scale16='fusion_low_q', high_scale=T,
                      history_H=H, history_M=M, history_Z=Z, duration=duration,
                      output_hat='projected_Ahat', output_bound='fusion_output_bound'))
    if 'boundary_comparisons' in packet:
        packet['parent_boundary_comparisons'] = packet.pop('boundary_comparisons')
    compiler.recount(packet)
    compiler.check_source(packet)
    assert (packet['operations'], packet['equations'], packet['witnesses']) == (
        old['operations']-56, old['equations']-15, old['witnesses']-21)
    assert packet['multiplications'] == old['multiplications']-29
    assert packet['additions_subtractions'] == old['additions_subtractions']-27
    return packet


def build(*, merge_bound=True):
    return rewrite(parent.build('raw', merge_bound=merge_bound,
                                project_J=True, project_Ahat=True))


def polynomial_source(packet):
    assert packet['form'] == 'raw'
    return compiler.parent.polynomial_source(packet)


def degree_bound(packet):
    # Literal circuit bounds only: no on-zero equations or discarded roots.
    degree = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    d = lambda v: degree[v] if isinstance(v, str) else 0
    for n, op, a, b in packet['source']:
        degree[n] = d(a)+d(b) if op == '*' else max(d(a), d(b))
    maximum = max(max(d(a), d(b)) for a, b in packet['comparisons'])
    return dict(degree_upper_bound=2*maximum, maximum_residual_degree_bound=maximum,
                native_scale_degrees=[d('Q'), d('and__q')], exact_degree_claimed=False)


def ledger(packet):
    source, out = polynomial_source(packet)
    c = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    return dict(bound_is_program_E=packet['bound_is_program_E'],
        certificate={k: packet[k] for k in ('operations', 'multiplications', 'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=c['M'], additions_subtractions=c['A'], output=out),
        parameters=packet['parameters'], **degree_bound(packet))


def independent_audit(packet, values, constants):
    """Compare with one independently instantiated canonical AND64 source.

    This checks the new full polynomial itself, not equality to the old
    polynomial, whose separate native witnesses have different semantics.
    """
    old = packet['fusion_parent']
    old_values = dict(values, **{n: 1 for n in packet['fusion_removed_auxiliaries']})
    before = parent.independent_execute(old['source'], old_values, constants)
    source, out = polynomial_source(packet)
    after = parent.independent_execute(source, values, constants)
    I = packet['fusion_interfaces']
    B, S, ell = before['B'], before['scale'], before[I['duration']]
    L = B*S
    Hr = B*before['copies']+ell
    Mr = B*values['K']+ell-1
    Zr = B*(before['projected_Ahat']-1)
    Hh, Mh, Zh, T = (before[I[n]] for n in ('history_H', 'history_M', 'history_Z', 'high_scale'))
    joined = dict(P=L*T, Hhat=Hr+L*Hh+1, Mhat=Mr+L*Mh+1, Zhat=Zr+L*Zh+1)
    _, auxiliary = native.domains('and64_prescribed')
    joined.update({n: values['and__'+n] for n in auxiliary})
    ns, np, _ = native.source('and64_prescribed')
    exact = native.parent.execute(ns, joined)
    for n in ('q', 'F3', 'padded_A', 'padded_B'):
        assert after['and__'+n] == exact[n]
    for n, _, _, _ in ns:
        if n not in ('scaled_A', 'scaled_B', 'scaled_Z'):
            assert after['and__'+n] == exact[n], n
    get = lambda v,e: e[v] if isinstance(v,str) else v
    nr = {('and__'+a, 'and__'+b): exact[a]-exact[b] for a,b in np}
    expected = []
    for a, b in packet['comparisons']:
        if (a,b) in nr:
            expected.append(nr[a,b])
        elif a == 'fusion_output_bound':
            expected.append(before['projected_Ahat']+values[SLACK]-S)
        else:
            expected.append(get(a,before)-get(b,before))
    actual = [get(a,after)-get(b,after) for a,b in packet['comparisons']]
    assert actual == expected
    assert after[out] == sum(r*r for r in expected)
    # All old outer/geometry rows and comparisons keep their values. Only
    # the surviving AND extension is changed, not the ordinary input loader.
    for n, _, _, _ in old['source']:
        if not n.startswith(('and__', HISTORY_PREFIX)):
            assert before[n] == after[n], n
    return after


def split_checks():
    """Finite algebra tests, independent of all native Pell witnesses."""
    rng = random.Random(356246)
    count = invalid = 0
    for ell in range(0, 8):
        L = 1 << ell
        for _ in range(128):
            Hr, Mr, Zr = (rng.randrange(L) for _ in range(3))
            Hh, Mh, Zh = (rng.randrange(128) for _ in range(3))
            expected = (Hr & Mr) == Zr and (Hh & Mh) == Zh
            assert (((Hr+L*Hh) & (Mr+L*Mh)) == Zr+L*Zh) == expected
            actual_low, actual_high = Hr & Mr, Hh & Mh
            assert ((Hr+L*Hh) & (Mr+L*Mh)) == actual_low+L*actual_high
            count += 1
            invalid += not expected
    return dict(canonical_split_cases=count, rejected_random_outputs=invalid)


def positive_outer_checks():
    """Genuine recoder bits and affine paths; native coordinates are placeholders."""
    import binary_tag_four_tile_history as tag
    import pcp_affine_slope_class_history as selected
    rng = random.Random(2463764)
    history = parent.history.rewrite_history(tag.build()['raw_packet']['history_packet'])
    checked = 0
    for k in (3, 4, 7):
        for n in (2, 4, 8):
            q = 1 << n
            Q = q**k
            B = (1 << (k-1))*Q
            P = B**n
            J = (P-1)//(B-1)
            S = q*P
            K = (S-1)//(2*B-1)
            assert (2*B-1)*K+1 == S
            for _ in range(12):
                x = rng.randrange(1,q)
                A = (x*J) & K
                Ahat = A+1
                beta = S-Ahat
                assert beta > 0
                L = B*S
                Hr, Mr, Zr = B*x*J+n, B*K+n-1, B*A
                assert 0 <= Hr < L and 0 <= Mr < L and 0 <= Zr < L
                assert Hr & Mr == Zr
                word = tuple(rng.randrange(4) for _ in range(rng.randrange(1,7)))
                v = selected.positive_outer_fixture(history,word,rng.randrange(1,6))
                e = native.parent.execute(history['source'],v)
                Hh,Mh,Zh,T = (e[history['interfaces'][key]] for key in ('H','M','Z','scale'))
                assert Hh & Mh == Zh and 0 <= max(Hh,Mh,Zh) < T
                H,M,Z = Hr+L*Hh,Mr+L*Mh,Zr+L*Zh
                assert H & M == Z and max(H,M,Z) < L*T
                assert (L*T) & (L*T-1) == 0
                checked += 1
    return checked


def verify():
    rng = random.Random(356151205)
    cases = signed = 0
    records = []
    for merged in (False, True):
        packet = build(merge_bound=merged)
        records.append(ledger(packet))
        for case in range(192):
            positive = case < 96
            values = {n: rng.randrange(1,5) if positive else rng.randrange(-3,4)
                      for n in packet['parameters']+packet['auxiliaries']}
            constants = {n: rng.randrange(1,8) if positive else rng.randrange(-5,6)
                         for n in compiler.NUMERALS}
            if positive:
                constants['recoder_radix'], constants['repunit_divisor'] = 4,7
            after = independent_audit(packet, values, constants)
            if positive:
                assert after['and__q'] > 0 and after['and__F3'] >= 8
            cases += 1
            signed += not positive
    packet = build()
    record = ledger(packet)
    assert (packet['operations'], packet['equations'], packet['witnesses']) == (246,37,64)
    assert record['polynomial']['operations'] == 356
    # Rejections make the deleted-core/private-interface obligations executable.
    old = parent.build('raw')
    bad = [dict(old, source=old['source']+[('forbidden_core_use','+',HISTORY_PREFIX+'q',1)]),
           dict(old, comparisons=old['comparisons']+[(HISTORY_PREFIX+'F0','q')]),
           dict(old, source=[(n,'+',a,b) if n == 'and__q' else (n,op,a,b) for n,op,a,b in old['source']]),
           dict(old, project_Ahat=False), packet]
    for broken in bad:
        try: rewrite(broken)
        except (AssertionError,KeyError): pass
        else: raise AssertionError('invalid fusion contract accepted')
    source,out = polynomial_source(packet)
    encoded = compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_JOINT_AND', ledgers=records,
        independent_canonical_and_full_output_identities=cases, signed_cases=signed,
        split_checks=split_checks(), genuine_outer_concatenations=positive_outer_checks(),
        rejected_source_contracts=len(bad),
        source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest(),
        example=dict(source=encoded,output=out,comparisons=packet['comparisons'],
                     parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        scope='Complete fixed U9 ordinary-input raw polynomial through one joint AND '
              'and one independent geometry core. Existential outer-coordinate '
              'equivalence uses fresh native extensions; no off-zero identity to the '
              'old two-AND polynomial or full witness bijection is claimed. Numerical '
              'tests do not construct full positive Pell zeros.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['ledgers'][-1])
