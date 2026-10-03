"""Reuse the edge checksum's internal-plus-first sum in sparse state flow."""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import group_projective_port_bias_folding as ports
import group_projective_joint_bound_unit as joint

execute = ports.execute
residuals = ports.residuals


def rewrite(old):
    groups = old['flow']['groups']
    if not groups['internal']:
        return dict(old, shared_flow_target=True, shared_flow_target_saving=0,
                    shared_flow_removed_registers=[], shared_flow_replacement=[])
    rows = {row[0]: row for row in old['source']}
    def raw(tag):
        edges = groups[tag]
        assert edges
        return f'controller__edge_hat{edges[0]}' if len(edges) == 1 else f'controller__flow_raw_{tag}{len(edges)-1}'
    raw_internal, raw_first = raw('internal'), raw('first')
    checksum = 'controller__flow_checksum1'
    assert rows[checksum] == (checksum, '+', raw_internal, raw_first)
    first = sorted((old['edges'][e][1], e) for e in groups['first'])
    assert first and first[0][0] == 1
    assert all(first[i][0] < first[i+1][0] for i in range(len(first)-1))
    assert all(old['edges'][e][0] == 0 for _, e in first)
    shift = len(first) >= 2 and first[1][0] == 2
    removed = set()
    def old_product(coefficient, edge):
        variable = f'controller__edge_hat{edge}'
        if coefficient == 1: return variable
        name = f'controller__flow_first_product{edge}'
        assert rows[name] == (name, '*', coefficient, variable)
        removed.add(name)
        return name
    terms = ([raw_first]+[old_product(c-1, e) for c, e in first[1:]] if shift
             else [old_product(c, e) for c, e in first])
    value = terms[0]
    for i, term in enumerate(terms[1:], 1):
        name = f'controller__flow_weighted_first{i}'
        assert rows[name] == (name, '+', value, term)
        removed.add(name)
        value = name
    prefixes = ('controller__flow_first_', 'controller__flow_weighted_first')
    assert {n for n in rows if n.startswith(prefixes)} == removed
    partial, target = 'controller__flow_target_partial', 'controller__flow_target'
    shared = 'controller__flow_shared'
    assert rows[partial] == (partial, '+', shared, raw_internal)
    assert rows[target] == (target, '+', partial, value)
    removed.add(partial)
    consumers = {n: {user for user, _, a, b in old['source'] if n in (a, b)} for n in removed}
    assert all(users <= removed | {target} for users in consumers.values())
    assert not any(n in pair for n in removed for pair in old['comparisons'])
    # First-state weights begin at one: F=raw_first+sum_(later first e)(state_e-1)*Ehat_e.
    replacement = []
    terms = [checksum]
    for i, (coefficient, edge) in enumerate(first[1:], 1):
        variable = f'controller__edge_hat{edge}'
        coefficient -= 1
        if coefficient == 1:
            term = variable
        else:
            term = f'shared_flow_excess{i}'
            replacement.append((term, '*', coefficient, variable))
        terms.append(term)
    value = shared
    for i, term in enumerate(terms, 1):
        name = target if i == len(terms) else f'shared_flow_target_sum{i}'
        replacement.append((name, '+', value, term))
        value = name
    source = [row for row in old['source'] if row[0] not in removed | {target}]+replacement
    source = ports.shared.factored.index.parent.sort_source(source, {'x', *old['auxiliaries']})
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M': old['multiplications'], 'A': old['additions_subtractions']-1}
    assert len(source) == old['operations']-1
    return dict(old, source=source, operations=len(source), multiplications=counts['M'],
        additions_subtractions=counts['A'], shared_flow_target=True, shared_flow_target_saving=1,
        shared_flow_first_weights=first, shared_flow_parent_used_shift=shift,
        shared_flow_removed_registers=sorted(removed), shared_flow_replacement=replacement,
        shared_flow_private_consumers={n: sorted(v) for n, v in sorted(consumers.items())})


def build(codes, alpha=24, beta=12, variant='joint', controller_mask=False, compute_length=False):
    if variant == 'joint':
        old = joint.build(codes, alpha, beta, controller_mask, compute_length)
    else:
        old = ports.build(codes, alpha, beta, variant, controller_mask, compute_length)
    return rewrite(old)


def polynomial_source(packet):
    return (joint if packet.get('joint_bound_unit_merged') else ports).polynomial_source(packet)


def degree_top(packet, w):
    return (joint if packet.get('joint_bound_unit_merged') else ports).degree_top(packet, w)


def verify():
    examples = [(), ((1, 2),), ((1, 2), (3, 4)), ((1, 2, 3),),
                ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),),
                ((1, 2), (3, 4, 5)), ((1, 2, 3), (4, 5)),
                ((1,), (2, 3, 4), (5,), (6, 7, 8), (1, 2))]
    records, cases, example = [], 0, None
    rng = random.Random(2763504)
    for codes in examples:
      for variant in ('four', 'six', 'shifted', 'strong', 'joint'):
       for reuse in (False, True):
        if reuse and ports.build(codes)['m'] < 8: continue
        for comp in (False, True):
            old = (joint.build(codes, controller_mask=reuse, compute_length=comp) if variant == 'joint'
                   else ports.build(codes, variant=variant, controller_mask=reuse, compute_length=comp))
            packet = rewrite(old)
            source, out = polynomial_source(packet)
            prior, prior_out = polynomial_source(old)
            saving = int(any(len(code) >= 3 for code in codes))
            assert packet['shared_flow_target_saving'] == saving
            assert len(source) == len(prior)-saving
            assert packet['auxiliaries'] == old['auxiliaries'] and packet['comparisons'] == old['comparisons']
            for case in range(24):
                z = {n: rng.randrange(1, 6) if case < 16 else rng.randrange(-4, 5)
                     for n in packet['parameters']+packet['auxiliaries']}
                env, before = execute(source, z), execute(prior, z)
                assert all(env[n] == before[n] for n, _, _, _ in source if n in before)
                assert residuals(packet, env) == residuals(old, before)
                assert env[out] == before[prior_out]
                # Independently reconstruct the actual sparse target state word.
                target = sum(edge[1]*(z[f'controller__edge_hat{i}']-1) for i, edge in enumerate(packet['edges']))
                if saving:
                    assert env['controller__flow_target'] == target
                cases += 1
            w = {n: 1+i % 3 for i, n in enumerate(packet['parameters']+packet['auxiliaries'])}
            w['selection__tau_gap'] = 1
            degree = degree_top(packet, w)[0]
            counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
            records.append(dict(m=packet['m'], variant=variant, controller_mask=reuse, compute_length=comp,
                internal_edges=packet['flow']['internal_edges'], nontrivial_paths=packet['flow']['nontrivial_paths'],
                flow_saving=saving, port_saving=packet['port_bias_saving']['operations'],
                certificate_operations=packet['operations'], polynomial_operations=len(source),
                polynomial_M=counts['M'], polynomial_A=counts['A'], equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'], exact_degree=degree))
            if codes == examples[4] and variant == 'joint' and reuse and comp:
                example = dict(packet, polynomial_finalizer=source[packet['operations']:], polynomial_output=out)
                assert (packet['operations'], len(source), degree, packet['positive_witnesses']) == (259, 276, 3504, 42)
    return dict(status='PASS_GROUP_PROJECTIVE_SHARED_FLOW_TARGET', records=records, source_example=example,
        complete_register_residual_and_polynomial_identity_cases=cases, signed_assignments=cases//3,
        scope='One addition saved whenever the fixed macro table has an internal edge. Complete output polynomial and supplied coordinates unchanged. No new universal numerical alphabet or global optimality claim.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
