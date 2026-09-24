#!/usr/bin/env python3
"""Three masked fields suffice for fixed permutation routing."""
from collections import Counter
from itertools import permutations, product
from pathlib import Path
import json
import sympy as sp

import explore_fixed_program_routing as old
import explore_base_three_pell_kernel as kernel
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives


def constants(f, initial=0, final=0):
    m = len(f)
    assert m >= 3 and m % 2 == 1
    assert sorted(f) == list(range(m)) and all(f[i] != i for i in range(m))
    spacing = 1
    while 3**spacing <= m + 1:
        spacing += 1
    a = [spacing * 3**i for i in range(m)]
    d = max(a)
    positions = [d + a[f[i]] - a[i] for i in range(m)]
    assert len(set(positions)) == m and min(positions) >= 0
    S = sum(3**j for j in a)
    g = 3**d
    K = sum(3**j for j in positions)
    B, W = 2, 9
    while W <= max((K+g)*S, 2*S+1):
        B += 2
        W *= 9
    return dict(f=list(f), a=a, d=d, spacing=spacing, g=g, K=K, S=S,
                B=B, W=W, initial=initial, final=final,
                initial_word=3**a[initial], final_word=3**a[final])


PROGRAM = constants([1, 2, 0], 0, 2)
OUTER_NAMES = [x for x in old.OUTER_NAMES if x != 'Rep']
SYM = {x: value for x, value in old.SYM.items() if x != 'Rep'}


def build(c=PROGRAM, permutation=True):
    # Copy only the counted outer geometry, bounds and routing. Restate every
    # polynomial below, including the changed three-field mask input.
    W, S, K, g, I, F = [c[x] for x in
                         ['W', 'S', 'K', 'g', 'initial_word', 'final_word']]
    complement = (W-1)//2-S
    assert complement > 0
    prefix = [
        ('qm1', '*', W-1, 'H'), ('q_rhs', '+', 'qm1', 1),
        ('complement_H', '*', complement, 'H'),
        ('input_rhs', '+', 'C', 'complement_H'),
    ] + old.build(c)[0][6:15]
    packing = [
        ('pack0', '*', 'q', 'TestV'), ('pack1', '+', 'TestC', 'pack0'),
        ('pack2', '*', 'q', 'pack1'), ('P0', '+', 'C', 'pack2'),
    ] if permutation else old.build(c)[0][15:21]
    ops = prefix + packing + kernel.OUTER + kernel.CORE
    tests = [('q', 'q_rhs'), ('TestC', 'input_rhs'),
             ('junk_lhs', 'TestV'), ('routing_lhs', 'routing_rhs'),
             ('bound_lhs', 'q')] + kernel.EQUALITIES
    q, H, C, V, TC, TV, alpha = [SYM[x] for x in ['q']+OUTER_NAMES]
    packed = C+q*TC+q*q*TV if permutation else C+q*V+q*q*TC+q**3*TV
    source = [q-(W-1)*H-1, TC-C-complement*H,
              V+g*S*H-TV, (W*K-g)*C+g*I-g*F*q-W*V, TC+TV+alpha-q]
    sub = {kernel.SYM[x]: SYM[x] for x in kernel.CORE_NAMES}
    sub.update({kernel.SYM['q']: q, kernel.SYM['P0']: packed})
    source.extend(p.subs(sub, simultaneous=True) for p in kernel.source_residuals())
    return ops, tests, source


def certificate(permutation=True):
    c = PROGRAM if permutation else old.PROGRAM
    ops, tests, source = build(c, permutation)
    env = dict(SYM)
    histogram = baseline.run_schedule(ops, env)
    correction = source[-3]*((2*SYM['r']+1+SYM['j']*SYM['c'])**2-SYM['y_aux']**2)
    records = []
    for index, ((left, right), p) in enumerate(zip(tests, source)):
        extra = correction if index == len(source)-2 else sp.Integer(0)
        assert sp.expand(env[left]-env[right]-p-extra) == 0, index
        records.append(dict(index=index, equality=[left, right],
                            source=sp.sstr(p), correction=sp.sstr(extra)))
    primitive, counts = verify_primitives(ops, env)
    operation_count = 66 if permutation else 68
    expected = {'+': 29, '*': 37} if permutation else {'+': 30, '*': 38}
    assert len(primitive) == operation_count and counts == expected
    assert len(tests) == len(source) == 16
    used = {x for row in ops for x in row[2:]} | {x for pair in tests for x in pair}
    assert set(SYM) <= used
    assert len(OUTER_NAMES+kernel.CORE_NAMES) == 23
    # Exact witness elimination in the unchanged outer relation.
    Rep = sp.Symbol('Rep')
    W, S = c['W'], c['S']
    H, C, TC = SYM['H'], SYM['C'], SYM['TestC']
    old_support = C+Rep-S*H-TC
    old_rep = Rep-((W-1)//2)*H
    assert sp.expand(source[1]+old_support-old_rep) == 0
    return dict(operations=operation_count, primitive_histogram=counts, histogram=histogram,
                parameters=['q'], positive_unknowns=OUTER_NAMES+kernel.CORE_NAMES,
                equations=16, instructions=primitive, residuals=records,
                program=c, masked_fields=['C', 'TestC', 'TestV'] if permutation
                else ['C', 'V', 'TestC', 'TestV'])


def subset_words(c):
    return [sum(3**c['a'][i] for i in range(len(c['f'])) if bits >> i & 1)
            for bits in range(1 << len(c['f']))]


def coefficient_checks(c):
    m, a, d = len(c['f']), c['a'], c['d']
    positions = [d+a[c['f'][k]]-a[k] for k in range(m)]
    count = 0
    for bits, C in enumerate(subset_words(c)):
        coefficients = Counter(p+a[i] for p in positions
                               for i in range(m) if bits >> i & 1)
        assert max(coefficients.values(), default=0) <= m
        assert all(e % c['spacing'] == 0 for e in coefficients)
        normalized = c['K']*C
        assert normalized < c['W']
        for j in range(m):
            target = d+a[j]
            expected = int(bool(bits >> c['f'].index(j) & 1))
            assert coefficients[target] == expected
            assert normalized // 3**target % 3 == expected
            count += 1
    return count


def canonical(c, height, initial):
    W, S, g, K = [c[x] for x in ['W', 'S', 'g', 'K']]
    state = initial
    rows, nextrows = [], []
    for _ in range(height):
        rows.append(3**c['a'][state])
        state = c['f'][state]
        nextrows.append(3**c['a'][state])
    q = W**height
    H, Rep = (q-1)//(W-1), (q-1)//2
    C = sum(row*W**j for j, row in enumerate(rows))
    Next = sum(row*W**j for j, row in enumerate(nextrows))
    V = K*C-g*Next
    TC, TV = C+Rep-S*H, V+g*S*H
    alpha = q-TC-TV
    assert min(H, Rep, C, V, TC, TV, alpha) > 0
    assert TC == C+((W-1)//2-S)*H
    assert all(old.boolean(x) and x < q for x in [C, V, TC, TV])
    assert V % 2 == 0
    assert (W*K-g)*C+g*rows[0] == g*nextrows[-1]*q+W*V
    packed = C+q*TC+q*q*TV
    assert 0 < packed < q**3 and packed % 2 == 0 and old.boolean(packed)
    r = 9*q**4-3*packed-1
    assert r % 2 == 0 and old.v3central(r) == 4*c['B']*height+2
    return state


def regression():
    coefficient_cases = canonical_cases = candidates = accepted = 0
    tested_maps = []
    for m in [3, 5]:
        for f in permutations(range(m)):
            if any(f[i] == i for i in range(m)):
                continue
            c = constants(f)
            coefficient_cases += coefficient_checks(c)
            tested_maps.append(c)
            for initial, height in product(range(m), range(1, 5)):
                canonical(c, height, initial)
                canonical_cases += 1
    # All source subsets are tested without imposing one-hot or V Booleanity.
    adversarial = [c for c in tested_maps if len(c['f']) == 3]
    adversarial += [c for c in tested_maps if len(c['f']) == 5][:2]
    for c in adversarial:
        W, S, K, g = [c[x] for x in ['W', 'S', 'K', 'g']]
        q, H = W*W, W+1
        Rep = (q-1)//2
        words = subset_words(c)
        m = len(c['f'])
        for initial, final in product(range(m), repeat=2):
            I, F = 3**c['a'][initial], 3**c['a'][final]
            for low, high in product(words, repeat=2):
                candidates += 1
                C = low+W*high
                V, remainder = divmod((W*K-g)*C+g*I-g*F*q, W)
                if remainder or min(C, V) <= 0:
                    continue
                TC, TV = C+Rep-S*H, V+g*S*H
                alpha = q-TC-TV
                if min(TC, TV, alpha) <= 0:
                    continue
                assert 0 < C < TC < q and V < TV < q
                packed = C+q*TC+q*q*TV
                assert 0 < packed < q**3
                r = 9*q**4-3*packed-1
                if old.v3central(r) < 8*c['B']+2:
                    continue
                accepted += 1
                assert low == I and high == 3**c['a'][c['f'][initial]]
                assert c['f'][c['f'][initial]] == final
                assert old.boolean(V)
    assert accepted == sum(len(c['f']) for c in adversarial)
    return dict(permutation_tables=len(tested_maps),
                normalized_subset_target_checks=coefficient_cases,
                canonical_histories=canonical_cases,
                adversarial_subset_histories=candidates,
                accepted_complete_candidates=accepted,
                scope='All fixed-point-free permutations on 3 and 5 states for normalized target checks; all subsets of two rows on both 3-state maps and two 5-state maps, with no V mask or one-hot guard in acceptance. Full positive Pell tuples are supplied by theorem, not instantiated.')


def verify():
    return dict(status='PASS_PERMUTATION_PROGRAM_ROUTING_COMPONENT',
                arithmetic=certificate(), general_arithmetic=certificate(False),
                regression=regression(), general_regression=old.regression(),
                proof='../1980/EXPLORATION_PERMUTATION_PROGRAM_ROUTING.md',
                scope='Complete 66-operation fixed permutation path relation and equivalent 68-operation general fixed graph path relation. Counter branches, raw input and a universal compiler remain outside these counts.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print(result['arithmetic']['operations'], result['arithmetic']['primitive_histogram'])
    print(result['general_arithmetic']['operations'], result['general_arithmetic']['primitive_histogram'])
    print(result['regression'])
