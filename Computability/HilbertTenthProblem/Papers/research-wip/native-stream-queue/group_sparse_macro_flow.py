"""Share hub-path state weights and already-paid edge-checksum sums.

Every comparison residual, and hence every literal SOS polynomial, agrees
with the dense parent on arbitrary integer assignments. Only the state
flow and the addition tree of the existing checksum change. Native cores,
positive witnesses and all25/controller60/complete comparisons remain.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_regular_macro_controller as controller
import group_complete_matrix_compiler as complete


def groups(edges):
    result = {'internal':[], 'first':[], 'last':[], 'hub':[]}
    states = set()
    for index, (a, b, _) in enumerate(edges):
        states.update(v for v in (a, b) if v)
        tag = 'internal' if a and b else 'last' if a else 'first' if b else 'hub'
        if tag == 'internal':
            assert b == a+1
        result[tag].append(index)
    n = len(states)
    assert states == set(range(1, n+1))
    for state in states:
        assert sum(e[0] == state for e in edges) == 1
        assert sum(e[1] == state for e in edges) == 1
    b = len(result['first'])
    assert b == len(result['last'])
    assert len(result['internal']) == n-b
    return result, n, b


def rewrite_controller(old):
    edges, m = old['edges'], old['m']
    partition, n, b = groups(edges)
    checksum_source, flow_source = [], []

    def emit(where, name, op, left, right):
        where.append((name, op, left, right))
        return name

    def summed(where, terms, prefix):
        if not terms:
            return 0
        result = terms[0]
        for index, value in enumerate(terms[1:], 1):
            result = emit(where, f'{prefix}{index}', '+', result, value)
        return result

    raw = {tag:summed(checksum_source, [f'edge_hat{i}' for i in indices],
                      'flow_raw_'+tag)
           for tag, indices in partition.items()}
    total = summed(checksum_source, [raw[tag] for tag in partition if partition[tag]],
                   'flow_checksum')
    assert len(checksum_source) == m-1

    def fixed_product(coefficient, value, name):
        assert coefficient >= 1
        return value if coefficient == 1 else emit(flow_source, name, '*', coefficient, value)

    savings = {}
    def weighted(tag, coordinate):
        terms = sorted((edges[i][coordinate], i) for i in partition[tag])
        if not terms:
            savings[tag] = 0
            return 0
        assert all(c > 0 for c, _ in terms) and len({c for c, _ in terms}) == len(terms)
        shift = len(terms) >= 2 and terms[1][0] == terms[0][0]+1
        savings[tag] = int(shift)
        if shift:
            least = terms[0][0]
            values = [fixed_product(least, raw[tag], f'flow_{tag}_base')]
            values += [fixed_product(c-least, f'edge_hat{i}', f'flow_{tag}_product{i}')
                       for c, i in terms[1:]]
        else:
            values = [fixed_product(c, f'edge_hat{i}', f'flow_{tag}_product{i}') for c, i in terms]
        return summed(flow_source, values, 'flow_weighted_'+tag)

    if n == 0:
        pair = (0, 0)
        expected = {'M':0, 'A':0}
    elif n == 1:
        # The existing B-1 is shared directly; both hat offsets disappear.
        left = emit(flow_source, 'flow_left', '+', raw['last'], 'cell_minus1')
        right = emit(flow_source, 'flow_right', '*', 'B', raw['first'])
        pair = (left, right)
        expected = {'M':1, 'A':1}
    else:
        V = weighted('internal', 0)
        F = weighted('first', 1)
        L = weighted('last', 0)
        correction = n*(n+1)//2
        if partition['internal']:
            shared = emit(flow_source, 'flow_shared', '-', V, correction)
            left = emit(flow_source, 'flow_left', '+', shared, L)
            target = emit(flow_source, 'flow_target_partial', '+', shared, raw['internal'])
            target = emit(flow_source, 'flow_target', '+', target, F)
            expected = {'M':n+b-1-sum(savings.values()), 'A':n+b+1}
        else:
            left = emit(flow_source, 'flow_left', '-', L, correction)
            target = emit(flow_source, 'flow_target', '-', F, correction)
            assert b == n and savings == {'internal':0, 'first':1, 'last':1}
            expected = {'M':2*n-3, 'A':2*n}
        right = emit(flow_source, 'flow_right', '*', 'B', target)
        pair = (left, right)
    actual = Counter('M' if op == '*' else 'A' for _, op, _, _ in flow_source)
    assert all(actual[key] == expected[key] for key in ('M', 'A'))
    assert len(flow_source) <= 2*n+2*b

    old_source = old['source']
    cs_start = next(i for i, row in enumerate(old_source) if row[0] == 'edge_sum1')
    cs_end = cs_start+m-1
    assert all(row[0].startswith('edge_sum') for row in old_source[cs_start:cs_end])
    flow_start = next(i for i, row in enumerate(old_source) if row[0] == 'source_weighted0')
    flow_end = next(i for i, row in enumerate(old_source) if row[0] == 'shifted_target')+1
    assert flow_end-flow_start == 4*m+1
    source = (old_source[:cs_start]+checksum_source+old_source[cs_end:flow_start]
              +flow_source+old_source[flow_end:])
    pairs = list(old['comparisons'])
    assert pairs[16] == ('source_word', 'shifted_target')
    pairs[2] = (total, pairs[2][1])
    pairs[16] = pair
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    h, p = old['h'], old['projection_additions']
    assert counts == {'M':m+2*h+29+actual['M'], 'A':2*m+h+p+30+actual['A']}
    assert len(source) == 3*m+3*h+p+59+len(flow_source)
    available = set(old['parameters']+old['auxiliaries'])
    for name, op, left, right in source:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert len(pairs) == 25
    packet = dict(old)
    packet.update(source=source, comparisons=pairs, operations=len(source),
                  multiplications=counts['M'], additions_subtractions=counts['A'],
                  flow=dict(internal_states=n, nontrivial_paths=b,
                            internal_edges=n-b, groups=partition,
                            checksum_instructions=checksum_source, instructions=flow_source,
                            weighted_sum_savings=savings, operations=len(flow_source),
                            multiplications=actual['M'], additions_subtractions=actual['A'],
                            dense_operations=4*m+1, saved_operations=4*m+1-len(flow_source)))
    return packet


def build_controller(codes):
    codes = tuple(tuple(code) for code in codes)
    packet = rewrite_controller(controller.build(controller.macro_table(codes)))
    packet['codes'] = codes
    return packet


def build_complete(codes, alpha=24, beta=12):
    codes = tuple(tuple(code) for code in codes)
    old = complete.build(codes, alpha, beta)
    ctrl = build_controller(codes)
    prefix = old['aliases']['controller']
    def rename(value):
        return value if isinstance(value, int) else prefix.get(value, 'controller__'+value)
    source, pairs, blocks = [], [], []
    for block in old['blocks']:
        start, length = block['instruction_start'], block['instruction_count']
        cstart, clength = block['comparison_start'], block['comparison_count']
        if block['name'] == 'controller':
            instructions = [(rename(n), op, rename(a), rename(b)) for n, op, a, b in ctrl['source']]
            comparisons = [(rename(a), rename(b)) for a, b in ctrl['comparisons']]
        else:
            instructions = old['source'][start:start+length]
            comparisons = old['comparisons'][cstart:cstart+clength]
        blocks.append(dict(block, instruction_start=len(source), instruction_count=len(instructions),
                           comparison_start=len(pairs), comparison_count=len(comparisons)))
        source += instructions
        pairs += comparisons
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    m, h, p, flow = old['m'], old['h'], old['projection_additions'], ctrl['flow']
    assert counts == {'M':m+2*h+127+flow['multiplications'],
                      'A':2*m+h+p+145+flow['additions_subtractions']}
    assert len(source) == 3*m+3*h+p+272+flow['operations']
    assert len(pairs) == 60 and len(old['auxiliaries']) == m+87
    packet = dict(old)
    packet.update(source=source, comparisons=pairs, blocks=blocks, operations=len(source),
                  multiplications=counts['M'], additions_subtractions=counts['A'], flow=flow)
    return packet


def identity_checks():
    rng = random.Random(251660)
    examples = [(), ((1,),), ((1, 2),), ((1, 2), (3, 4)),
                ((1, 2, 3),), ((1, 2, 3, 4, 5),),
                ((1, 2), (3, 4, 5), (6, 7, 8, 1))]
    examples += [tuple(tuple(rng.randrange(1, 9) for _ in range(rng.randrange(1, 9)))
                       for _ in range(rng.randrange(1, 7))) for _ in range(24)]
    cases = 0
    for codes in examples:
        old = controller.build(controller.macro_table(codes))
        new = build_controller(codes)
        assert old['parameters'] == new['parameters'] and old['auxiliaries'] == new['auxiliaries']
        # An exact symbolic identity for every changed comparison, at this table.
        syms = {name:sp.Symbol(name) for name in old['parameters']+old['auxiliaries']}
        oldenv = controller.execute(old['source'], syms)
        newenv = controller.execute(new['source'], syms)
        for index in (2, 16):
            lhs = controller.residuals(old, oldenv)[index]
            rhs = controller.residuals(new, newenv)[index]
            assert sp.expand(lhs-rhs) == 0
        new_sos, out = controller.polynomial_source(new)
        for case in range(64):
            z = {name:rng.randrange(1, 21) if case < 48 else rng.randrange(-9, 10)
                 for name in old['parameters']+old['auxiliaries']}
            env = controller.execute(new_sos, z)
            expected = controller.manual_residuals(old, z)
            assert controller.residuals(new, env) == expected
            assert env[out] == sum(v*v for v in expected)
            cases += 1
    return dict(tables=len(examples), full_controller_residual_assignments=cases,
                symbolic_changed_residuals_per_table=2,
                identities='Every25 residual and the SOS equal the dense parent on arbitrary integer assignments.')


def complete_checks():
    rng = random.Random(60451)
    examples = [(), ((1, 2),), ((1, 2), (3, 4)),
                ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),),
                ((1, 2), (3, 4, 5), (6, 7, 8, 1))]
    packets = []
    t = sp.Symbol('t')
    cases = 0
    for codes in examples:
        new = build_complete(codes)
        sos, out = complete.polynomial_source(new)
        m, h, p, flow = new['m'], new['h'], new['projection_additions'], new['flow']
        counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in sos)
        assert len(sos) == 3*m+3*h+p+451+flow['operations']
        assert counts == {'M':new['multiplications']+60,'A':new['additions_subtractions']+119}
        for case in range(128):
            z = {name:rng.randrange(1, 14) if case < 96 else rng.randrange(-7, 8)
                 for name in new['parameters']+new['auxiliaries']}
            env = complete.execute(sos, z)
            expected = complete.independent_residuals(new, z, env)
            assert complete.residuals(new, env) == expected
            assert env[out] == sum(v*v for v in expected)
            cases += 1
        names = new['parameters']+new['auxiliaries']
        scales = {name:1+i % 3 for i, name in enumerate(names)}
        values = {name:sp.Poly(scales[name]*t+i+1,t) for i,name in enumerate(names)}
        env = complete.execute(sos, values)
        degree = max(112, 12*m+16)
        s = scales
        select_top = s['selection__w']**2*s['selection__s']**4*s['selection__k']**2*(16*s['P']**8)**6
        ctrl_top = s['controller__w']**2*s['controller__s']**4*s['controller__k']**2*(8*s['J']*s['P']**(m-1))**6
        top = (select_top**2 if degree == 112 else 0)+(ctrl_top**2 if degree == 12*m+16 else 0)
        assert env[out].degree() == degree and env[out].LC() == top
        new['sum_of_squares'] = dict(operations=len(sos), multiplications=counts['M'],
                                     additions_subtractions=counts['A'], exact_degree=degree,
                                     weighted_leading_coefficient=str(top), output=out)
        packets.append(new)
    return dict(packets=packets, full_complete_residual_assignments=cases,
                exact_polynomial_degree='max(112,12m+16)')


def verify():
    return dict(status='PASS_GROUP_SPARSE_MACRO_FLOW', identities=identity_checks(),
                complete=complete_checks(),
                controller_comparison_operations='3m+3h+p+59+flow',
                complete_comparison_operations='3m+3h+p+272+flow',
                complete_polynomial_operations='3m+3h+p+451+flow',
                uniform_flow_bound='flow<=2n+2b<=2L; n=L-number_of_codes, b=number_of_codes_of_length_at_least2',
                scope='Identical positive solution sets and identical polynomials to the complete parent; all native cores remain separate.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write', action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
