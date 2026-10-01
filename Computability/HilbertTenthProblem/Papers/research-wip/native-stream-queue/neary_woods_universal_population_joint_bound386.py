"""Join the two positive Q bounds in the complete U9 population compiler.

Q=q+z+gap restores both parent slacks positively. Conversely the parent's
typed spread bound implies Q>q+z, so every parent zero has a positive gap.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_population_projection389 as parent
from native_binary_input_dilation_unit179 import sort_source

compiler = parent.compiler
D = parent.D
BOUND = ('output_bound', 'Q')


def rewrite(old):
    assert old.get('population_width') and old['width'] >= 3
    assert old['form'] in ('raw', 'units', 'normalized')
    q = 'q' if old['form'] == 'raw' else 'input_bound'
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    assert rows['Q'] == ('+', q, 'power_gap')
    assert rows['B'] == ('*', compiler.Numeral('recoder_radix'), 'Q')
    assert old['fixed_numerals']['recoder_radix'] == '2^(D-1)'
    assert rows['output_bound'] == ('+', 'z', 'output_slack')
    assert 'z' in old['auxiliaries'] and 'power_gap' in old['auxiliaries']
    assert old['auxiliaries'].count('output_slack') == 1
    assert [n for n, _, a, b in old['source'] if 'output_slack' in (a, b)] == ['output_bound']
    assert [n for n, _, a, b in old['source'] if 'power_gap' in (a, b)] == ['Q']
    assert not any('output_slack' in pair or 'power_gap' in pair for pair in old['comparisons'])
    assert not any('output_bound' in (a, b) for _, _, a, b in old['source'])
    assert [pair for pair in old['comparisons'] if 'output_bound' in pair] == [BOUND]
    assert not {'output_bound', 'output_slack'} & set(old.get('public_registers', {}).values())
    assert 'joined_scale_floor' not in rows
    if old['form'] == 'raw':
        assert 'q' in old['auxiliaries']
    else:
        assert rows['input_bound'] == ('+', 'x', 'input_slack')
    source = []
    for n, op, a, b in old['source']:
        if n == 'output_bound':
            source.append(('joined_scale_floor', '+', q, 'z'))
        elif n == 'Q':
            source.append(('Q', '+', 'joined_scale_floor', 'power_gap'))
        else:
            source.append((n, op, a, b))
    aux = [n for n in old['auxiliaries'] if n != 'output_slack']
    source = sort_source(source, old['parameters']+aux)
    packet = dict(old, source=source, auxiliaries=aux,
                  comparisons=[p for p in old['comparisons'] if p != BOUND],
                  joint_scale_parent=old, q_input_register=q,
                  joined_Q_bounds=True, power_gap_semantics='Q-q-z',
                  parent_width_constraint_operations=old.get('width_constraint_operations'),
                  width_constraint_operations=3)
    if 'boundary_comparisons' in old:
        boundary = old['boundary_comparisons']
        packet['boundary_comparisons'] = boundary-int(old['comparisons'].index(BOUND) < boundary)
    compiler.recount(packet)
    compiler.check_source(packet)
    assert packet['operations'] == old['operations']
    assert packet['multiplications'] == old['multiplications']
    assert packet['additions_subtractions'] == old['additions_subtractions']
    assert packet['equations'] == old['equations']-1
    assert packet['witnesses'] == old['witnesses']-1
    return packet


def build(form='normalized', *, merge_bound=True, project_J=True, project_Ahat=True):
    return rewrite(parent.build(form, merge_bound=merge_bound,
                                project_J=project_J, project_Ahat=project_Ahat))


def degree_bound(packet):
    # Q and the new floor remain degree one. This is a fresh propagation
    # over the actual changed rows, including every norm-cancellation guard.
    return parent.degree_bound(packet)


def ledger(packet):
    source, output = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    old = packet['joint_scale_parent']
    old_source, _ = compiler.parent.polynomial_source(old)
    old_counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in old_source)
    assert len(source) == len(old_source)-3
    assert counts['M'] == old_counts['M']-1 and counts['A'] == old_counts['A']-2
    return dict(form=packet['form'], project_J=packet['project_J'],
        project_Ahat=packet['project_Ahat'], bound_is_program_E=packet['bound_is_program_E'],
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=output),
        parameters=packet['parameters'], **degree_bound(packet))


def lift(packet, values):
    env = compiler.parent.execute(packet['source'], values)
    g, z = values['power_gap'], values['z']
    q = env[packet['q_input_register']]
    return dict(values, power_gap=z+g, output_slack=q+g)


def project(old_values):
    """Positive at parent zeros by the full spread theorem, not on every tuple."""
    return {n: v if n != 'power_gap' else v-old_values['z']
            for n, v in old_values.items() if n != 'output_slack'}


def audit_identity(old, packet, values):
    after = compiler.parent.execute(packet['source'], values)
    restored = lift(packet, values)
    before = compiler.parent.execute(old['source'], restored)
    assert before['output_bound'] == before['Q'] == after['Q']
    assert all(before[n] == after[n] for n, _, _, _ in packet['source']
               if n != 'joined_scale_floor')
    get = compiler.parent.scalar
    assert [get(a, after)-get(b, after) for a, b in packet['comparisons']] == [
        get(a, before)-get(b, before) for a, b in old['comparisons'] if (a, b) != BOUND]
    old_source, old_out = compiler.parent.polynomial_source(old)
    source, out = compiler.parent.polynomial_source(packet)
    assert compiler.parent.execute(old_source, restored)[old_out] == compiler.parent.execute(source, values)[out]
    assert project(restored) == values
    return restored


def verify():
    rng = random.Random(386188198)
    records, identities, signed, positive_lifts = [], 0, 0, 0
    materialize_packet = parent.parent.parent.materialize_packet
    for form in ('raw', 'units', 'normalized'):
        for merge_bound in (False, True):
            for pj, pa in ((False, False), (False, True), (True, False), (True, True)):
                packet = build(form, merge_bound=merge_bound, project_J=pj, project_Ahat=pa)
                old = packet['joint_scale_parent']
                records.append(ledger(packet))
                for case in range(24):
                    pos = case < 12
                    constants = {n: rng.randrange(1, 8) if pos else rng.randrange(-5, 6)
                                 for n in compiler.NUMERALS}
                    values = {n: rng.randrange(1, 6) if pos else rng.randrange(-4, 5)
                              for n in packet['parameters']+packet['auxiliaries']}
                    literal = materialize_packet(packet, constants)
                    old_literal = literal['joint_scale_parent']
                    restored = audit_identity(old_literal, literal, values)
                    if pos:
                        assert all(v > 0 for v in restored.values())
                        positive_lifts += 1
                    identities += 1
                    signed += not pos
    # Exact converse inequality on genuine spread values. These are outer
    # families, not materialized full native zeros or the giant fixed D.
    outer = 0
    for width in (3, 4, 7, 13, 31):
        for n in (2, 4, 8):
            q = 1 << n
            Q = q**width
            for x in range(1, q):
                z = sum(((x >> j)&1) << (width*j) for j in range(n))
                assert z*((1 << width)-1) <= Q-1
                assert 4*q <= Q and 7*z < Q and q+z < Q
                g = Q-q-z
                assert g > 0 and z+g == Q-q and q+g == Q-z
                outer += 1
    # The converse is deliberately not claimed on arbitrary parent tuples.
    old_values = dict(z=2, power_gap=1, output_slack=1)
    assert project(old_values)['power_gap'] == -1
    packet = build()
    record = ledger(packet)
    assert record['polynomial'] == dict(operations=386, multiplications=188,
                                       additions_subtractions=198, output='history_output')
    assert packet['equations'] == 21 and packet['witnesses'] == 66
    source, output = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POPULATION_JOINT_BOUND386',
        ledgers=records, complete_certificate_residual_and_output_identities=identities,
        signed_cases=signed, unconditionally_positive_lifts=positive_lifts,
        exact_spread_converse_bound_families=outer,
        arbitrary_parent_inverse_need_not_be_positive=True,
        fixed_recipe=parent.parent.parent.u9.components()[-1],
        source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
        example=dict(source=encoded, output=output, comparisons=packet['comparisons'],
                     parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        scope='One fixed ordinary-input universal polynomial:386=188M198A,21 comparisons,'
              '66 positive witnesses,four program parameters,degree at most2241. '
              'Q=q+z+positivegap restores both old Q bounds; converse positivity uses '
              'the actual parent spread theorem. All fixed coefficients and encodings '
              'are unchanged, with exact complete-output identities under the lift.')


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
