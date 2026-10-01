"""Erase paid positive kernel definitions from the projective range compiler.

The four-definition variant keeps the parent's degree. The six-definition
variant saves two additional equations at the price of a higher degree.
Both transformations are exact graph substitutions, including off zeros.
"""
import argparse
from collections import Counter
import heapq
import json
from pathlib import Path
import random

import sympy as sp
import group_range_projective_compiler as parent

execute = parent.shared.execute
residuals = parent.shared.residuals
polynomial_source = parent.shared.polynomial_source


VARIANTS = {
    'four': ('a', 'd', 'k', 's'),
    'six': ('a', 'c', 'd', 'k', 'r', 's'),
}


def build(codes, alpha=24, beta=12, variant='six'):
    old = parent.build(codes, alpha, beta)
    wanted = {f'selection__{name}' for name in VARIANTS[variant]}
    substitutions, removed = {}, []
    for index, (left, right) in enumerate(old['comparisons']):
        if left in wanted and left not in substitutions:
            substitutions[left] = right
            removed.append(index)
    assert substitutions.keys() == wanted
    assert all(name in old['auxiliaries'] for name in wanted)
    def replace(value):
        return substitutions.get(value, value) if isinstance(value, str) else value
    source = [(name, op, replace(left), replace(right))
              for name, op, left, right in old['source']]
    pairs = [(replace(left), replace(right))
             for index, (left, right) in enumerate(old['comparisons']) if index not in removed]
    aux = [name for name in old['auxiliaries'] if name not in wanted]
    supplied = {'x', *aux}
    producers = {name: index for index, (name, _, _, _) in enumerate(source)}
    assert not supplied.intersection(producers) and len(producers) == len(source)
    users = [[] for _ in source]
    pending, ready = [], []
    for index, (_, _, left, right) in enumerate(source):
        dependencies = {x for x in (left, right) if isinstance(x, str) and x not in supplied}
        assert dependencies <= producers.keys()
        pending.append(len(dependencies))
        for dependency in dependencies:
            users[producers[dependency]].append(index)
        if not dependencies:
            heapq.heappush(ready, index)
    ordered, positions = [], []
    while ready:
        index = heapq.heappop(ready)
        ordered.append(source[index]); positions.append(index)
        for user in users[index]:
            pending[user] -= 1
            if pending[user] == 0:
                heapq.heappush(ready, user)
    assert len(ordered) == len(source), 'cyclic graph substitution'
    packet = dict(old)
    packet.update(source=ordered, comparisons=pairs, auxiliaries=aux,
                  equations=len(pairs), positive_witnesses=len(aux), variant=variant,
                  computed_kernel_coordinates=substitutions,
                  deleted_residual_indices=removed,
                  inherited_residual_indices=[i for i in range(len(old['comparisons'])) if i not in removed],
                  original_topological_positions=positions)
    assert packet['equations'] == 26-len(wanted)
    assert packet['positive_witnesses'] == packet['m']+40-len(wanted)
    return packet


def extend(packet, values, env):
    return dict(values, **{key: env[value] if isinstance(value, str) else value
                          for key, value in packet['computed_kernel_coordinates'].items()})


def verify():
    rng = random.Random(220206)
    records, assignments, positives, signed = [], 0, 0, 0
    for codes in ((), ((1,), (2,)), ((1, 2), (3, 4)),
                  ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),)):
        old = parent.build(codes)
        old_sos, old_out = polynomial_source(old)
        for variant in VARIANTS:
            new = build(codes, variant=variant)
            sos, out = polynomial_source(new)
            k, m = len(VARIANTS[variant]), new['m']
            counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in sos)
            assert len(sos) == new['operations']+3*(26-k)-1
            assert counts == {'M': new['multiplications']+26-k,
                              'A': new['additions_subtractions']+2*(26-k)-1}
            assert len(old_sos)-len(sos) == 3*k
            for case in range(256):
                z = {key: rng.randrange(1, 13) if case < 192 else rng.randrange(-6, 7)
                     for key in new['parameters']+new['auxiliaries']}
                env = execute(sos, z)
                restored = extend(new, z, env)
                oldenv = execute(old_sos, restored)
                before, after = residuals(old, oldenv), residuals(new, env)
                assert all(before[i] == 0 for i in new['deleted_residual_indices'])
                assert after == [before[i] for i in new['inherited_residual_indices']]
                assert env[out] == oldenv[old_out] == sum(r*r for r in after)
                assert all(env[name] == oldenv[name] for name, _, _, _ in new['source'])
                if case < 192:
                    assert all(restored[key] > 0 for key in new['computed_kernel_coordinates'])
                    positives += 1
                else:
                    signed += 1
                assignments += 1
            t = sp.Symbol('t')
            weights = {name: 1+i % 3 for i, name in enumerate(new['parameters']+new['auxiliaries'])}
            z = {name: sp.Poly(value*t+i+1, t) for i, (name, value) in enumerate(weights.items())}
            env = execute(sos, z)
            L = m+18
            qtop = 16*weights['P']**L
            ktop = weights['selection__eta']+weights['selection__zeta']
            stop = 2*weights['selection__odd_half']
            if variant == 'four':
                degree = 12*m+232
                top = weights['selection__w']**2*stop**4*ktop**2*qtop**6
            else:
                degree = 24*m+444
                ctop = ktop*stop*qtop
                rtop = 16**4*weights['H2']*weights['P']**(4*L-3)
                top = weights['selection__i']**2*ctop**4*(2*rtop)**2
            assert env[out].degree() == degree, (m, variant, env[out].degree(), degree)
            assert env[out].LC() == top**2, (m, variant, 'highest coefficient')
            new['sum_of_squares'] = dict(operations=len(sos), multiplications=counts['M'],
                                         additions_subtractions=counts['A'], exact_degree=degree,
                                         weighted_leading_coefficient=str(top**2), output=out)
            records.append(new)
    return dict(status='PASS_GROUP_PROJECTIVE_COMPUTED_KERNEL_FIELDS', packets=records,
                complete_graph_substitution_and_SOS_assignments=assignments,
                positive_graph_extensions=positives, signed_identity_assignments=signed,
                scope='Positive solution bijections over the complete projective range compiler; no explicit numerical universal alphabet.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = json.loads(json.dumps(verify())); path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
