"""The complete U9 population-width polynomial with its redundant bound removed."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_population_tag as parent
import native_binary_population_width_bound188 as bound

compiler = parent.compiler
D = parent.D


def build(form='normalized', *, merge_bound=True):
    assert form in ('raw', 'units', 'normalized')
    packet = bound.remove_bound(parent.build('raw', merge_bound=merge_bound))
    if form != 'raw':
        packet = compiler.parent.units.rewrite(packet)
        packet.update(form='units', unit_product=True)
        if form == 'normalized':
            packet = compiler.parent.normalized.rewrite(packet)
            packet['form'] = 'normalized'
    compiler.check_source(packet)
    assert bound.BOUND_AUX not in packet['auxiliaries']
    assert bound.BOUND_ROW[0] not in {n for n, _, _, _ in packet['source']}
    return packet


def degree_bound(packet):
    # The removed degree-one bound never controlled a parent maximum.
    # This reruns the parent's actual row propagation and all norm guards.
    return parent.degree_bound(packet)


def ledger(packet):
    source, output = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    expected = {'raw': (309, 55, 88, 473, 207, 266),
                'units': (318, 27, 69, 398, 188, 210),
                'normalized': (324, 24, 69, 395, 191, 204)}[packet['form']]
    assert (packet['operations'], packet['equations'], packet['witnesses'],
            len(source), counts['M'], counts['A']) == expected
    return dict(form=packet['form'], width=D,
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=output),
        parameters=packet['parameters'], bound_is_program_E=packet['bound_is_program_E'],
        **degree_bound(packet))


def lift(packet, values):
    """Integer slack restoration, positive at zeros but possibly signed elsewhere."""
    env = compiler.parent.execute(packet['source'], values)
    return dict(values, **{bound.BOUND_AUX: env['geometry_index']-env['B']})


def audit_identity(old, packet, values):
    lifted = lift(packet, values)
    before = compiler.parent.execute(old['source'], lifted)
    after = compiler.parent.execute(packet['source'], values)
    assert packet['source'] == [row for row in old['source'] if row[0] != bound.BOUND_ROW[0]]
    assert all(before[n] == after[n] for n, _, _, _ in packet['source'])
    assert before[bound.BOUND_ROW[0]] == before['geometry_index']
    assert packet['comparisons'] == [p for p in old['comparisons'] if p != bound.BOUND_PAIR]
    scalar = compiler.parent.scalar
    residuals = [scalar(a, after)-scalar(b, after) for a, b in packet['comparisons']]
    assert residuals == [scalar(a, before)-scalar(b, before)
                         for a, b in old['comparisons'] if (a, b) != bound.BOUND_PAIR]
    osource, oout = compiler.parent.polynomial_source(old)
    source, out = compiler.parent.polynomial_source(packet)
    assert compiler.parent.execute(osource, lifted)[oout] == compiler.parent.execute(source, values)[out]
    return lifted


def verify():
    rng = random.Random(395191204)
    ledgers = []
    identities = signed = negative_lifts = raw_manual = corrections = 0
    for merge_bound in (False, True):
        for form in ('raw', 'units', 'normalized'):
            old = parent.build(form, merge_bound=merge_bound)
            packet = build(form, merge_bound=merge_bound)
            ledgers.append(ledger(packet))
            assert packet['fixed_numerals'] == old['fixed_numerals']
            assert packet['parameters'] == old['parameters']
            constants = {n: rng.randrange(-7, 8) for n in compiler.NUMERALS}
            old_literal = parent.materialize_packet(old, constants)
            literal = parent.materialize_packet(packet, constants)
            for case in range(64):
                values = {n: rng.randrange(1, 5) if case < 32 else rng.randrange(-3, 4)
                          for n in packet['parameters']+packet['auxiliaries']}
                lifted = audit_identity(old_literal, literal, values)
                identities += 1
                signed += case >= 32
                negative_lifts += lifted[bound.BOUND_AUX] < 0
                if form == 'raw':
                    expected = parent.independent_raw(old, lifted, constants)
                    index = old['comparisons'].index(bound.BOUND_PAIR)
                    assert expected[index] == 0
                    expected = expected[:index]+expected[index+1:]
                    env = compiler.parent.execute(literal['source'], values)
                    scalar = compiler.parent.scalar
                    assert expected == [scalar(a, env)-scalar(b, env)
                                        for a, b in literal['comparisons']]
                    raw_manual += 1
                elif form == 'units':
                    compiler.parent.units.audit_identity(literal, values)
                    corrections += 1
                else:
                    compiler.parent.normalized.audit_identity(literal, values)
                    restored = compiler.parent.normalized.lift(literal, values)
                    compiler.parent.units.audit_identity(literal['parent_packet'], restored)
                    corrections += 1
    # The positivity implication does not need any Pell equation or typing.
    positive_implications = 0
    for k in (3, 7, 31, 257):
        for _ in range(64):
            x, input_slack, gap, v, E, duration_gap = [rng.randrange(1, 17) for _ in range(6)]
            Q = x+input_slack+gap
            B = (1 << (k-1))*Q
            duration = E+duration_gap
            J = (B-1)*v+duration
            R = ((1 << k)-1)*J
            assert J >= B and R >= 7*B > B > Q
            positive_implications += 1
    packet = build()
    source, output = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(source)
    table, counts, machine, summary, recipe = parent.u9.components()
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POPULATION_BOUND395',
        fixed_recipe=recipe, actual_machine=machine, cts=summary, tag_counts=counts,
        ledgers=ledgers,
        complete_source_residual_and_output_projection_cases=identities,
        signed_cases=signed, negative_off_zero_slack_lifts=negative_lifts,
        independent_complete_raw_residual_cases=raw_manual,
        complete_unit_and_normalization_correction_cases=corrections,
        untyped_positive_duration_implications=positive_implications,
        source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
        example=dict(source=encoded, output=output, comparisons=packet['comparisons'],
                     parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        scope='One fixed ordinary-input universal polynomial:395=191M204A,24 equations,'
              '69 positive witnesses,four program parameters,degree at most2204. '
              'Only the private geometry index bound is removed from the399 source. '
              'Its slack restores positively at zeros via the retained duration equation; '
              'the exact source/output identity also holds for signed off-zero lifts.')


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
