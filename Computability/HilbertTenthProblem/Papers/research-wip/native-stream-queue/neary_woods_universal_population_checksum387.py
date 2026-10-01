"""Merge the padded history checksum after proving its negative unit impossible.

The complete polynomial changes off zero; its explicit correction is audited.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_population_projection389 as parent

compiler = parent.compiler
CHECKSUM = 'hist__and__bs_q'


def rewrite(old):
    assert old['form'] in ('units', 'normalized') and old.get('population_width')
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    p = 'hist__and__'
    guards = {
        p+'q': ('*', 16, 'hist__P11__99'),
        p+'scaled_A': ('*', 16, 'hist__joined_H__89'),
        p+'padded_A': ('+', p+'scaled_A', 12),
        p+'scaled_B': ('*', 16, 'hist__joined_M__95'),
        p+'padded_B': ('+', p+'scaled_B', 10),
        p+'scaled_Z': ('*', 16, 'hist__joined_Z__96'),
        p+'F3': ('+', p+'scaled_Z', 8),
        p+'input_A': ('+', p+'F1', p+'F3'),
        p+'input_B': ('+', p+'F2', p+'F3'),
        p+'shared_sum02': ('+', p+'F0', p+'F2'),
        p+'bs_Q': ('+', p+'shared_sum02', p+'input_A'),
        CHECKSUM: ('-', p+'q', p+'bs_Q'),
    }
    assert all(rows.get(n) == row for n, row in guards.items())
    assert all(p+'F'+str(i) in old['auxiliaries'] for i in range(3))
    assert (p+'input_A', p+'padded_A') in old['comparisons']
    assert (p+'input_B', p+'padded_B') in old['comparisons']
    assert (CHECKSUM, 1) in old['comparisons']
    assert old['comparisons'][-1] == (old['unit_register'], 1)
    assert CHECKSUM not in old['unit_factors'] and 'and__bs_q' in old['unit_factors']
    name = 'padded_checksum_all_units'
    assert name not in rows
    source = old['source']+[(name, '*', old['unit_register'], CHECKSUM)]
    pairs = [pair for pair in old['comparisons'][:-1] if pair != (CHECKSUM, 1)]+[(name, 1)]
    packet = dict(old, source=source, comparisons=pairs, unit_register=name,
                  unit_factors=old['unit_factors']+[CHECKSUM], checksum_parent=old,
                  padded_checksum_sign=True)
    compiler.recount(packet)
    compiler.check_source(packet)
    assert packet['operations'] == old['operations']+1
    assert packet['equations'] == old['equations']-1
    assert packet['witnesses'] == old['witnesses']
    return packet


def build(form='normalized', *, merge_bound=True, project_J=True, project_Ahat=True):
    return rewrite(parent.build(form, merge_bound=merge_bound,
                                project_J=project_J, project_Ahat=project_Ahat))


def degree_bound(packet):
    old = packet['checksum_parent']
    record = parent.degree_bound(old)
    degrees = {n: 1 for n in old['parameters']+old['auxiliaries']}
    d = lambda v: degrees[v] if isinstance(v, str) else 0
    for n, op, a, b in old['source']:
        degrees[n] = d(a)+d(b) if op == '*' else max(d(a), d(b))
    # No norm cancellation is needed to bound this checksum. The inherited
    # complete degree proof checks all main norm cancellations separately.
    extra = d(CHECKSUM)
    assert extra == 44
    return dict(degree_upper_bound=record['degree_upper_bound']+extra,
                unit_degree_bound=record['unit_degree_bound']+extra,
                maximum_residual_degree_bound=record['maximum_residual_degree_bound'],
                added_checksum_degree_bound=extra, exact_degree_claimed=False)


def ledger(packet):
    source, output = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    oldsource, _ = compiler.parent.polynomial_source(packet['checksum_parent'])
    oc = Counter('M' if op == '*' else 'A' for _, op, _, _ in oldsource)
    assert len(source) == len(oldsource)-2
    assert (counts['M'], counts['A']) == (oc['M'], oc['A']-2)
    return dict(form=packet['form'], project_J=packet['project_J'],
                project_Ahat=packet['project_Ahat'], bound_is_program_E=packet['bound_is_program_E'],
                certificate={k: packet[k] for k in ('operations', 'multiplications',
                         'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(source), multiplications=counts['M'],
                         additions_subtractions=counts['A'], output=output),
                parameters=packet['parameters'], **degree_bound(packet))


def sign_fixtures():
    cases = 0
    minimum_excess = 100
    # Exhaust all compositions of the high-part sum for n<=8. Every resulting
    # tuple satisfies the negative checksum and all prescribed low residues.
    for n in range(4, 9):
        q = 1 << n
        high_sum = (1 << (n-4))-1
        for a in range(high_sum+1):
            for b in range(high_sum-a+1):
                for c in range(high_sum-a-b+1):
                    high = (a, b, c, high_sum-a-b-c)
                    fields = [16*h+l for h, l in zip(high, (3, 4, 2, 8))]
                    assert sum(fields) == q+1 and all(0 < f < q for f in fields)
                    r = sum(f*q**i for i, f in enumerate(fields))
                    assert r.bit_count() == sum(f.bit_count() for f in fields)
                    excess = r.bit_count()-n
                    assert excess >= 1
                    minimum_excess = min(minimum_excess, excess)
                    cases += 1
    assert minimum_excess == 1
    return dict(negative_checksum_compositions=cases, widths=list(range(4, 9)),
                minimum_population_excess=minimum_excess)


def verify():
    rng = random.Random(387189198)
    records, identities, signed = [], 0, 0
    for form in ('units', 'normalized'):
        for merge in (False, True):
            for j, a in ((False, False), (False, True), (True, False), (True, True)):
                packet = build(form, merge_bound=merge, project_J=j, project_Ahat=a)
                records.append(ledger(packet))
                old = packet['checksum_parent']
                osource, oout = compiler.parent.polynomial_source(old)
                source, out = compiler.parent.polynomial_source(packet)
                for case in range(32):
                    positive = case < 16
                    values = {n: rng.randrange(1, 5) if positive else rng.randrange(-3, 4)
                              for n in packet['parameters']+packet['auxiliaries']}
                    constants = {n: rng.randrange(1, 8) if positive else rng.randrange(-5, 6)
                                 for n in compiler.NUMERALS}
                    before = compiler.parent.execute(compiler.materialize(osource, constants), values)
                    after = compiler.parent.execute(compiler.materialize(source, constants), values)
                    assert all(before[n] == after[n] for n, _, _, _ in old['source'])
                    scalar = compiler.parent.scalar
                    retained = [pair for pair in old['comparisons'][:-1] if pair != (CHECKSUM, 1)]
                    S = sum((scalar(x, before)-scalar(y, before))**2 for x, y in retained)
                    U, C = before[old['unit_register']], before[CHECKSUM]
                    assert before[oout] == U*(1+S+(C-1)**2)-1
                    assert after[out] == U*C*(1+S)-1
                    assert before[oout]-after[out] == U*(C-1)*(C-2-S)
                    if positive:
                        assert after['hist__P__10'] >= 1
                        assert after['hist__and__q'] >= 16
                        assert after['hist__and__F3'] >= 8
                    identities += 1
                    signed += not positive
    packet = build()
    record = ledger(packet)
    assert record['polynomial']['operations'] == 387
    assert record['certificate']['witnesses'] == 67
    source, output = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(source)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_POPULATION_CHECKSUM387',
                ledgers=records, complete_polynomial_correction_cases=identities,
                signed_cases=signed, sign_fixtures=sign_fixtures(),
                source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                fixed_recipe=parent.parent.parent.u9.components()[-1],
                example=dict(source=encoded, output=output, comparisons=packet['comparisons'],
                         parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                         fixed_numeral_definitions=compiler.NUMERALS),
                scope='Conditional-on-retained-core sign proof excludes the history checksum -1. '
                      'One fixed U9 universal polynomial costs387=189M198A with67 positive '
                      'witnesses,21 comparisons,four program parameters and degree at most2285. '
                      'The parent and new complete polynomials differ off zero by the recorded '
                      'exact correction; their positive zero sets are identical.')


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
