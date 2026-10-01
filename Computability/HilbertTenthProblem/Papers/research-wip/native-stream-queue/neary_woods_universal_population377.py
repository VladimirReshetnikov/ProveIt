"""Compose positive joint bounds, shared history arithmetic and padded sign recovery."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_population_projection389 as parent
import neary_woods_universal_population_joint_bound386 as joint
import neary_woods_universal_shared_history382 as history
import neary_woods_universal_population_checksum387 as checksum

compiler = parent.compiler


def build(form='normalized', *, merge_bound=True, project_J=True,
          project_Ahat=True, merge_checksum=None):
    if merge_checksum is None:
        merge_checksum = form != 'raw'
    assert form != 'raw' or not merge_checksum
    original = parent.build(form, merge_bound=merge_bound,
                            project_J=project_J, project_Ahat=project_Ahat)
    packet = history.rewrite(joint.rewrite(original))
    if merge_checksum:
        packet = checksum.rewrite(packet)
    packet = dict(packet, complete_parent389=original,
                  combined_checksum=merge_checksum)
    compiler.check_source(packet)
    return packet


def degree_bound(packet):
    return checksum.degree_bound(packet) if packet['combined_checksum'] else parent.degree_bound(packet)


def ledger(packet):
    source, output = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    original = packet['complete_parent389']
    osource, _ = compiler.parent.polynomial_source(original)
    oc = Counter('M' if op == '*' else 'A' for _, op, _, _ in osource)
    merged = packet['combined_checksum']
    assert len(source) == len(osource)-10-2*merged
    assert counts['M'] == oc['M']-6 and counts['A'] == oc['A']-4-2*merged
    assert packet['witnesses'] == original['witnesses']-1
    assert packet['equations'] == original['equations']-1-merged
    assert packet['history_packet']['operations'] == 154
    return dict(form=packet['form'], merge_checksum=merged,
        project_J=packet['project_J'], project_Ahat=packet['project_Ahat'],
        bound_is_program_E=packet['bound_is_program_E'],
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=output),
        parameters=packet['parameters'], history_operations=154, **degree_bound(packet))


def independent_execute(source, values, constants):
    env = dict(values)
    def get(v):
        if isinstance(v, compiler.Numeral):
            return constants[v.name]
        return env[v] if isinstance(v, str) else v
    for name, op, a, b in source:
        assert name not in env
        x, y = get(a), get(b)
        env[name] = x*y if op == '*' else x+y if op == '+' else x-y
    return env


def verify():
    rng = random.Random(377183194)
    records, cases, signed, positives, commutations = [], 0, 0, 0, 0
    for form in ('raw', 'units', 'normalized'):
        for merge in (False, True):
            for jp, ap in ((False, False), (False, True), (True, False), (True, True)):
                for combine in ((False,) if form == 'raw' else (False, True)):
                    packet = build(form, merge_bound=merge, project_J=jp,
                                   project_Ahat=ap, merge_checksum=combine)
                    records.append(ledger(packet))
                    old = packet['complete_parent389']
                    source, out = compiler.parent.polynomial_source(packet)
                    osource, oout = compiler.parent.polynomial_source(old)
                    # Reverse the two independent source rewrites. Their
                    # compatible domains and identities make the order immaterial.
                    reverse = joint.rewrite(history.rewrite(old))
                    if combine:
                        reverse = checksum.rewrite(reverse)
                    rsource, rout = compiler.parent.polynomial_source(reverse)
                    assert reverse['comparisons'] == packet['comparisons']
                    assert reverse['auxiliaries'] == packet['auxiliaries']
                    for case in range(16):
                        pos = case < 8
                        values = {n: rng.randrange(1, 5) if pos else rng.randrange(-3, 4)
                                  for n in packet['parameters']+packet['auxiliaries']}
                        C = {n: rng.randrange(1, 8) if pos else rng.randrange(-5, 6)
                             for n in compiler.NUMERALS}
                        if pos:
                            C['recoder_radix'], C['repunit_divisor'] = 4, 7
                        q = values['q'] if form == 'raw' else values['x']+values['input_slack']
                        restored = dict(values, power_gap=values['z']+values['power_gap'],
                                        output_slack=q+values['power_gap'])
                        after = independent_execute(source, values, C)
                        before = independent_execute(osource, restored, C)
                        rev = independent_execute(rsource, values, C)
                        assert after[out] == rev[rout]
                        commutations += 1
                        ignored = {'hist__V_region__67'}
                        common = {r[0] for r in old['source']} & {r[0] for r in packet['source']}
                        assert all(before[n] == after[n] for n in common-ignored)
                        assert before['output_bound'] == before['Q'] == after['Q']
                        if combine:
                            unmerged = packet['checksum_parent']
                            get = lambda v: after[v] if isinstance(v, str) else v
                            pairs = [p for p in unmerged['comparisons'][:-1] if p != (checksum.CHECKSUM, 1)]
                            S = sum((get(a)-get(b))**2 for a, b in pairs)
                            U, c = after[unmerged['unit_register']], after[checksum.CHECKSUM]
                            assert before[oout]-after[out] == U*(c-1)*(c-2-S)
                        else:
                            assert before[oout] == after[out]
                        if pos:
                            assert all(v > 0 for v in restored.values())
                            if jp:
                                assert after['duration_J'] >= after['B']
                            if ap:
                                assert after['projected_Ahat'] >= 2
                            if form != 'raw':
                                assert after['hist__and__F3'] >= 8
                                assert after['hist__and__q'] >= 16
                            positives += 1
                        cases += 1
                        signed += not pos
    packet = build()
    record = ledger(packet)
    assert record['polynomial'] == dict(operations=377, multiplications=183,
                                        additions_subtractions=194, output='history_output')
    assert (packet['operations'], packet['equations'], packet['witnesses']) == (318, 20, 66)
    assert record['degree_upper_bound'] == 2285
    source, out = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POPULATION377', ledgers=records,
                complete_original_output_identities_or_corrections=cases,
                signed_cases=signed, positive_lift_cases=positives,
                complete_reversed_rewrite_output_identities=commutations,
                fixed_recipe=parent.parent.parent.u9.components()[-1],
                source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                example=dict(source=encoded, output=out, comparisons=packet['comparisons'],
                             parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                             fixed_numeral_definitions=compiler.NUMERALS),
                scope='One fixed U9 universal polynomial costs377=183M194A,66 positive '
                      'witnesses,20 comparisons,four positive program parameters and '
                      'degree at most2285. Keeping the independent checksum gives379 '
                      'operations at degree at most2241. All ordinary-input and exact '
                      'counter interfaces are inherited through the proved compositions.')


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
