"""Share the even history right-hand side with the odd one, saving 1M."""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_factored_native_index as factored
import group_projective_shifted_X_quotient as shifted

execute = factored.execute
residuals = factored.residuals


def rewrite(old):
    rows = {row[0]: row for row in old['source']}
    P = 'controller__geometry_power' if old['compute_length'] else 'P'
    expected = [
        ('history__c0', '-', 'D', 1),
        ('history__d0', '+', 'history__c0', 'history__u'),
        ('history__UP', '*', 'history__c0', P),
        ('history__right_even', '-', 'history__UP', 'D'),
        ('history__VP', '*', 'D', P),
        ('history__right_odd', '-', 'history__VP', 'history__d0'),
        ('controller__lane_factor0', '+', P, 1),
    ]
    assert all(rows[row[0]] == row for row in expected)
    private = {'history__d0', 'history__VP'}
    consumers = {n: {name for name, _, a, b in old['source'] if n in (a, b)}
                 for n in private}
    assert consumers == {n: {'history__right_odd'} for n in private}
    assert not any(n in pair for n in private for pair in old['comparisons'])
    source = []
    for name, op, a, b in old['source']:
        if name in private:
            continue
        if name == 'history__right_odd':
            source += [
                ('history__shared_odd_base', '+', 'history__right_even', 'controller__lane_factor0'),
                ('history__right_odd', '-', 'history__shared_odd_base', 'history__u'),
            ]
        else:
            source.append((name, op, a, b))
    source = factored.index.parent.sort_source(source, {'x', *old['auxiliaries']})
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M': old['multiplications'] - 1, 'A': old['additions_subtractions']}
    assert len(source) == old['operations'] - 1
    return dict(old, source=source, operations=len(source), multiplications=counts['M'],
                additions_subtractions=counts['A'], shared_history_rhs=True,
                removed_private_history_registers=sorted(private),
                audited_private_history_consumers={n: sorted(v) for n, v in sorted(consumers.items())})


def build(codes, alpha=24, beta=12, variant='shifted', controller_mask=False, compute_length=False):
    if variant == 'shifted':
        old = shifted.build(codes, alpha, beta, controller_mask, compute_length)
    else:
        assert variant in ('four', 'six')
        old = factored.build(codes, alpha, beta, variant, controller_mask, compute_length)
    return rewrite(old)


def polynomial_source(packet):
    return (shifted if packet.get('shifted_X_quotient') else factored).polynomial_source(packet)


def degree_top(packet, w):
    return (shifted if packet.get('shifted_X_quotient') else factored).degree_top(packet, w)


def verify():
    D, P, u = sp.symbols('D P u')
    even = (D - 1) * P - D
    old_odd = D * P - (D - 1 + u)
    new_odd = even + (P + 1) - u
    assert sp.expand(old_odd - new_odd) == 0
    rng = random.Random(2794298)
    records = []
    cases = 0
    example = None
    for codes in ((), ((1, 2), (3, 4)), ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),)):
      for variant in ('four', 'six', 'shifted'):
       for reuse in (False, True):
        if reuse and factored.build(codes)['m'] < 8:
            continue
        for comp in (False, True):
            if variant == 'shifted':
                old = shifted.build(codes, controller_mask=reuse, compute_length=comp)
            else:
                old = factored.build(codes, variant=variant, controller_mask=reuse, compute_length=comp)
            packet = rewrite(old)
            source, out = polynomial_source(packet)
            prior, prior_out = polynomial_source(old)
            assert packet['comparisons'] == old['comparisons']
            assert packet['auxiliaries'] == old['auxiliaries']
            assert len(source) == len(prior) - 1
            for case in range(64):
                z = {n: rng.randrange(1, 9) if case < 48 else rng.randrange(-5, 6)
                     for n in packet['parameters'] + packet['auxiliaries']}
                env = execute(source, z)
                before = execute(prior, z)
                assert all(env[n] == before[n] for n, _, _, _ in source if n in before)
                assert residuals(packet, env) == residuals(old, before)
                assert env[out] == before[prior_out]
                cases += 1
            w = {n: 1 + i % 3 for i, n in enumerate(packet['parameters'] + packet['auxiliaries'])}
            w['selection__tau_gap'] = 1
            degree = degree_top(packet, w)[0]
            assert degree == degree_top(old, w)[0]
            m, h, p = packet['m'], packet['h'], packet['projection_additions']
            C = 3 * m + 3 * h + p + 185 + packet['flow']['operations'] - 3 * min(h, 3) - reuse
            assert packet['operations'] == C - 2
            assert len(source) == C + {'four': 33, 'six': 27, 'shifted': 24}[variant] - 3 * comp
            counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
            prior_counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in prior)
            assert counts == {'M': prior_counts['M'] - 1, 'A': prior_counts['A']}
            records.append(dict(m=m, variant=variant, controller_mask=reuse, compute_length=comp,
                certificate_operations=packet['operations'], certificate_M=packet['multiplications'],
                certificate_A=packet['additions_subtractions'], equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'], polynomial_operations=len(source),
                polynomial_M=counts['M'], polynomial_A=counts['A'], exact_degree=degree,
                degree_justification='The entire final polynomial is identical to the parent by the audited history identity.'))
            if m == 16 and variant == 'shifted' and reuse and comp:
                example = dict(packet, polynomial_finalizer=source[packet['operations']:], polynomial_output=out)
                assert (packet['operations'], len(source), degree, packet['positive_witnesses']) == (256, 279, 4298, 42)
    return dict(status='PASS_GROUP_PROJECTIVE_SHARED_HISTORY_RHS',
        identity='D*P-(D-1+u)=((D-1)*P-D)+(P+1)-u',
        records=records, source_example=example,
        complete_register_residual_and_polynomial_identities=cases, signed_assignments=cases // 4,
        scope='One literal multiplication removed. All retained registers, residuals, final polynomials and positive witness vectors are unchanged. Universal numerical alphabet remains uninstantiated.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
