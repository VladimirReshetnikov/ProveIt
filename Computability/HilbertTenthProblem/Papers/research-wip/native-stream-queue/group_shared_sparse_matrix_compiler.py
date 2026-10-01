"""Combine shared typing, sparse flow and exact common geometric registers.

All47 residual polynomials agree identically with the shared-typing parent.
The full ordinary-input theorem and m+67 positive witnesses are unchanged.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_shared_typing_matrix_compiler as parent
import group_sparse_macro_flow as sparse


def build(codes, alpha=24, beta=12):
    codes = tuple(tuple(code) for code in codes)
    old = parent.build(codes, alpha, beta)
    ctrl = sparse.build_controller(codes)
    flow = ctrl['flow']
    m, h, p = old['m'], old['h'], old['projection_additions']
    global_names = {'B', 'P', 'J', *[f'Shat{i}' for i in range(8)]}
    def rename(value):
        return value if isinstance(value, int) or value in global_names else 'controller__'+value
    checksum = [(rename(n), op, rename(a), rename(b))
                for n, op, a, b in flow['checksum_instructions']]
    flow_source = [(rename(n), op, rename(a), rename(b))
                   for n, op, a, b in flow['instructions']]
    source = old['source']
    cs_start = next(i for i,row in enumerate(source) if row[0] == 'controller__edge_sum1')
    cs_end = cs_start+m-1
    fl_start = next(i for i,row in enumerate(source) if row[0] == 'controller__source_weighted0')
    fl_end = next(i for i,row in enumerate(source) if row[0] == 'controller__shifted_target')+1
    assert len(source[fl_start:fl_end]) == 4*m+1
    source = source[:cs_start]+checksum+source[cs_end:fl_start]+flow_source+source[fl_end:]
    pairs = list(old['comparisons'])
    pairs[24] = tuple(rename(v) for v in ctrl['comparisons'][2])
    pairs[25] = tuple(rename(v) for v in ctrl['comparisons'][16])
    before_cse = len(source)
    assert before_cse == 3*m+3*h+p+222+flow['operations']

    # Share only the specified power/repunit chains and the repeated B-1.
    # No native-core or unrelated algebraic CSE is performed here.
    allowed = {'controller__cell_minus1', 'selection__Bm1', 'joint_Pm',
               'selection__P2', 'selection__P4', 'selection__P8',
               'selection__J2', 'selection__P2plus1', 'selection__J4',
               'selection__P4plus1', 'selection__J8'}
    allowed.update(n for n, _, _, _ in source
                   if n.startswith(('controller__lane_power', 'controller__lane_factor',
                                    'controller__lane_repunit')))
    aliases, seen, rewritten, deleted = {}, {}, [], []
    def resolved(value):
        while isinstance(value, str) and value in aliases:
            value = aliases[value]
        return value
    for name, op, left, right in source:
        left, right = resolved(left), resolved(right)
        key = (op, left, right)
        if name in allowed and key in seen:
            aliases[name] = seen[key]
            deleted.append((name, op, left, right))
        else:
            rewritten.append((name, op, left, right))
            if name in allowed:
                seen[key] = name
    source = rewritten
    pairs = [(resolved(a), resolved(b)) for a, b in pairs]
    delta_M, delta_A = ((1, 2) if h == 1 else (3, 3) if h == 2 else (5, 4))
    removed_count = Counter('M' if op == '*' else 'A' for _, op, _, _ in deleted)
    assert removed_count == {'M':delta_M, 'A':delta_A}
    assert len(deleted) == 3*min(h, 3)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M':m+2*h+101+flow['multiplications']-delta_M,
                      'A':2*m+h+p+121+flow['additions_subtractions']-delta_A}
    assert len(source) == 3*m+3*h+p+222+flow['operations']-3*min(h, 3)
    available = {'x', *old['auxiliaries']}
    for name, op, left, right in source:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert len(pairs) == 47 and len(old['auxiliaries']) == m+67
    assert all(isinstance(v, int) or v in available for pair in pairs for v in pair)
    packet = dict(old)
    packet.update(source=source, comparisons=pairs, operations=len(source),
                  multiplications=counts['M'], additions_subtractions=counts['A'], flow=flow,
                  common_register_aliases=aliases, common_register_deletions=deleted,
                  common_register_saving=dict(multiplications=delta_M, additions_subtractions=delta_A,
                                              operations=len(deleted)),
                  saved_against_shared_parent=old['operations']-len(source))
    return packet


def verify():
    rng = random.Random(47362222)
    codesets = [(), ((1, 2),), ((1, 2), (3, 4)),
                ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),),
                ((1, 2), (3, 4, 5), (6, 7, 8, 1))]
    packets, cases = [], 0
    t = sp.Symbol('t')
    for codes in codesets:
        old, new = parent.build(codes), build(codes)
        assert old['auxiliaries'] == new['auxiliaries'] and old['parameters'] == new['parameters']
        sos, out = parent.polynomial_source(new)
        m, h, p = new['m'], new['h'], new['projection_additions']
        f, dm, da = new['flow'], new['common_register_saving']['multiplications'], new['common_register_saving']['additions_subtractions']
        counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in sos)
        assert counts == {'M':m+2*h+148+f['multiplications']-dm,
                          'A':2*m+h+p+214+f['additions_subtractions']-da}
        assert len(sos) == 3*m+3*h+p+362+f['operations']-3*min(h, 3)
        for case in range(256):
            z = {name:rng.randrange(1, 16) if case < 192 else rng.randrange(-7, 8)
                 for name in new['parameters']+new['auxiliaries']}
            oldenv = parent.execute(old['source'], z)
            newenv = parent.execute(sos, z)
            expected = parent.manual_residuals(new, z)
            assert parent.residuals(old, oldenv) == parent.residuals(new, newenv) == expected
            assert newenv[out] == sum(value*value for value in expected)
            for name, target in new['common_register_aliases'].items():
                assert oldenv[name] == newenv[target]
            cases += 1
        names = new['parameters']+new['auxiliaries']
        scales = {name:1+i % 3 for i, name in enumerate(names)}
        values = {name:sp.Poly(scales[name]*t+i+1, t) for i, name in enumerate(names)}
        env = parent.execute(sos, values)
        s = scales
        highest = s['selection__w']**2*s['selection__s']**4*s['selection__k']**2*(16*s['P']**(m+8))**6
        assert env[out].degree() == 12*m+112 and env[out].LC() == highest**2
        new['sum_of_squares'] = dict(operations=len(sos), multiplications=counts['M'],
                                     additions_subtractions=counts['A'], exact_degree=12*m+112,
                                     weighted_leading_coefficient=str(highest**2), output=out)
        packets.append(new)
    return dict(status='PASS_GROUP_SHARED_SPARSE_MATRIX_COMPILER', packets=packets,
                all_residual_and_SOS_parent_identities=cases, signed_assignments=cases//4,
                certificate_operations='3m+3h+p+222+f_flow-3min(h,3)',
                polynomial_operations='3m+3h+p+362+f_flow-3min(h,3)',
                positive_witnesses='m+67', equations=47, exact_degree='12m+112',
                equivalence='Every47 residual polynomial and the full SOS equal the shared-typing parent on arbitrary integer assignments.',
                scope='Complete fixed-table ordinary-input theorem; no numerically instantiated universal alphabet.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
