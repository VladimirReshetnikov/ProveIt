"""Eliminate eight positive selector-port coordinates by affine definitions.

No certificate gate is added or deleted. After stable topological reorder,
the remaining39 residuals equal the47-residual parent under the explicit
positive graph substitution, and the omitted eight residuals vanish.
"""
import argparse
from collections import Counter
import heapq
import json
from pathlib import Path
import random

import sympy as sp
import group_shared_sparse_matrix_compiler as parent


def build(codes, alpha=24, beta=12):
    old = parent.build(codes, alpha, beta)
    ports = {}
    for i, (left, right) in enumerate(old['comparisons'][26:34]):
        assert right == f'Shat{i}'
        ports[right] = left
    assert len(ports) == 8
    def replace(value):
        return ports.get(value, value) if isinstance(value, str) else value
    substituted = [(name, op, replace(left), replace(right))
                   for name, op, left, right in old['source']]
    pairs = [(replace(a), replace(b)) for i, (a, b) in enumerate(old['comparisons'])
             if not 26 <= i < 34]
    auxiliaries = [name for name in old['auxiliaries'] if name not in ports]
    assert len(old['auxiliaries'])-len(auxiliaries) == 8

    supplied = {'x', *auxiliaries}
    producer = {name:i for i, (name, _, _, _) in enumerate(substituted)}
    assert len(producer) == len(substituted) and not supplied.intersection(producer)
    users = [[] for _ in substituted]
    pending = []
    ready = []
    for index, (_, _, left, right) in enumerate(substituted):
        dependencies = {v for v in (left, right) if isinstance(v, str) and v not in supplied}
        assert dependencies <= producer.keys()
        pending.append(len(dependencies))
        for dependency in dependencies:
            users[producer[dependency]].append(index)
        if not dependencies:
            heapq.heappush(ready, index)
    source, positions = [], []
    while ready:
        index = heapq.heappop(ready)
        source.append(substituted[index]);positions.append(index)
        for user in users[index]:
            pending[user] -= 1
            if pending[user] == 0:
                heapq.heappush(ready, user)
    assert len(source) == len(substituted), 'cyclic selector substitution'
    available = set(supplied)
    for name, op, left, right in source:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert all(isinstance(v, int) or v in available for pair in pairs for v in pair)
    assert len(pairs) == 39 and len(auxiliaries) == old['m']+59
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M':old['multiplications'], 'A':old['additions_subtractions']}
    packet = dict(old)
    packet.update(source=source, comparisons=pairs, auxiliaries=auxiliaries,
                  equations=39, positive_witnesses=len(auxiliaries),
                  computed_selector_ports=ports,
                  inherited_residual_indices=[i for i in range(47) if not 26 <= i < 34],
                  deleted_port_residual_indices=list(range(26, 34)),
                  topological_original_positions=positions)
    return packet


def port_values(packet, values):
    """Independent affine formulas, before using any comparison."""
    return {f'Shat{i}':1+sum(values[f'controller__edge_hat{e}']-1
                             for e, edge in enumerate(packet['edges']) if edge[2] == i+1)
            for i in range(8)}


def verify():
    rng = random.Random(3933867)
    examples = [(), ((1,), (2,)), ((1, 2),), ((1, 2), (3, 4)),
                ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),),
                ((1, 2), (3, 4, 5), (6, 7, 8, 1))]
    packets, cases, positive, signed = [], 0, 0, 0
    t = sp.Symbol('t')
    for codes in examples:
        old, new = parent.build(codes), build(codes)
        old_sos, old_out = parent.parent.polynomial_source(old)
        sos, out = parent.parent.polynomial_source(new)
        m, h, p = new['m'], new['h'], new['projection_additions']
        flow = new['flow'];dm=new['common_register_saving']['multiplications'];da=new['common_register_saving']['additions_subtractions']
        assert len(sos) == 3*m+3*h+p+338+flow['operations']-3*min(h, 3)
        counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in sos)
        assert counts == {'M':m+2*h+140+flow['multiplications']-dm,
                          'A':2*m+h+p+198+flow['additions_subtractions']-da}
        assert len(old_sos)-len(sos) == 24
        for case in range(256):
            z = {name:rng.randrange(1, 17) if case < 192 else rng.randrange(-8, 9)
                 for name in new['parameters']+new['auxiliaries']}
            computed = port_values(new, z)
            extended = dict(z, **computed)
            oldenv = parent.parent.execute(old_sos, extended)
            newenv = parent.parent.execute(sos, z)
            old_residuals = parent.parent.residuals(old, oldenv)
            new_residuals = parent.parent.residuals(new, newenv)
            assert old_residuals[26:34] == [0]*8
            assert new_residuals == [old_residuals[i] for i in new['inherited_residual_indices']]
            manual = parent.parent.manual_residuals(old, extended)
            assert new_residuals == [manual[i] for i in new['inherited_residual_indices']]
            assert oldenv[old_out] == newenv[out] == sum(v*v for v in new_residuals)
            for name, expression in new['computed_selector_ports'].items():
                assert computed[name] == (expression if isinstance(expression, int) else newenv[expression])
            for name, _, _, _ in new['source']:
                assert newenv[name] == oldenv[name]
            if case < 192:
                assert min(computed.values()) >= 1
                positive += 1
            else:
                signed += 1
            cases += 1
        # Affine graph substitution cannot increase any old total degree;
        # the independent joined-norm highest form remains nonzero.
        names = new['parameters']+new['auxiliaries']
        weights = {name:1+i % 3 for i, name in enumerate(names)}
        z = {name:sp.Poly(weights[name]*t+i+1,t) for i, name in enumerate(names)}
        env = parent.parent.execute(sos, z)
        s = weights
        high = s['selection__w']**2*s['selection__s']**4*s['selection__k']**2*(16*s['P']**(m+8))**6
        assert env[out].degree() == 12*m+112 and env[out].LC() == high**2
        new['sum_of_squares'] = dict(operations=len(sos), multiplications=counts['M'],
                                     additions_subtractions=counts['A'], exact_degree=12*m+112,
                                     weighted_leading_coefficient=str(high**2), output=out)
        packets.append(new)
    return dict(status='PASS_GROUP_COMPUTED_SELECTOR_PORTS', packets=packets,
                full_graph_substitution_and_polynomial_identities=cases,
                strictly_positive_graph_extensions_checked=positive,
                signed_off_zero_identity_checks=signed,
                certificate_operations='3m+3h+p+222+f_flow-3min(h,3)',
                polynomial_operations='3m+3h+p+338+f_flow-3min(h,3)',
                equations=39, positive_witnesses='m+59', exact_degree='12m+112',
                equivalence='Positive solution sets are in bijection by erasure and the eight explicit affine graph coordinates.',
                scope='Complete fixed-table ordinary-input theorem; no numerical universal alphabet.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write', action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
