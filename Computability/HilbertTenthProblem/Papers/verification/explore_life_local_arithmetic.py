#!/usr/bin/env python3
"""Exact finite verification of an 18-operation packed Life local relation.

This is a local arithmetic component. Torus alignment, variable periods,
target encoding, Boolean masks, and positive representations of zero planes
are not included in its operation count.
"""
from itertools import product
from pathlib import Path
import json
import random


SCHEDULE = [
    ('N01', '+', 'n0', 'n1'),
    ('N012', '+', 'N01', 'n2'),
    ('N0123', '+', 'N012', 'n3'),
    ('N01234', '+', 'N0123', 'n4'),
    ('N012345', '+', 'N01234', 'n5'),
    ('N0123456', '+', 'N012345', 'n6'),
    ('N', '+', 'N0123456', 'n7'),
    ('u12', '+', 'u1', 'u2'),
    ('u12b', '-', 'u12', 'B'),
    ('m6', '*', 6, 'u12b'),
    ('m7', '*', 7, 'u3'),
    ('m11', '*', 11, 'u4'),
    ('m14', '*', 14, 'u5'),
    ('m22', '*', 22, 'Y'),
    ('lhs1', '+', 'N', 'm6'),
    ('lhs2', '+', 'lhs1', 'm7'),
    ('lhs', '+', 'lhs2', 'm22'),
    ('rhs', '+', 'm11', 'm14'),
]

# The same eleven-operation predicate when the inclusive nine-cell sum
# S=N+B is supplied. Exact torus shifts and its aggregation are separate.
INCLUSIVE_SCHEDULE = [
    ('u12', '+', 'u1', 'u2'),
    ('u3b', '-', 'u3', 'B'),
    ('m6', '*', 6, 'u12'),
    ('m7', '*', 7, 'u3b'),
    ('m11', '*', 11, 'u4'),
    ('m14', '*', 14, 'u5'),
    ('m22', '*', 22, 'Y'),
    ('lhs1', '+', 'S', 'm6'),
    ('lhs2', '+', 'lhs1', 'm7'),
    ('lhs', '+', 'lhs2', 'm22'),
    ('rhs', '+', 'm11', 'm14'),
]


def life(count, center):
    return int(count == 3 or count == 2 and center == 1)


def residual(count, center, target, u):
    return (count + 22*target + 6*(u[0]+u[1]-center)
            + 7*u[2] - 11*u[3] - 14*u[4])


def run(values,schedule=SCHEDULE):
    env = dict(values)
    for name,op,left,right in schedule:
        a = env[left] if isinstance(left,str) else left
        b = env[right] if isinstance(right,str) else right
        env[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def pack(values, radix=64):
    return sum(value*radix**i for i,value in enumerate(values))


def verify():
    auxiliary = list(product(range(2),repeat=5))
    solutions = {}
    count_tests = 0
    for count,center,target in product(range(9),range(2),range(2)):
        accepted = [u for u in auxiliary if residual(count,center,target,u) == 0]
        count_tests += len(auxiliary)
        assert bool(accepted) == (target == life(count,center))
        if accepted:
            solutions[count,center] = accepted

    histogram = {'*':0,'+':0}
    for _,op,_,_ in SCHEDULE:
        histogram['*' if op == '*' else '+'] += 1
    assert len(SCHEDULE) == 18 and histogram == {'*':5,'+':13}
    inclusive_histogram = {'*':0,'+':0}
    for _,op,_,_ in INCLUSIVE_SCHEDULE:
        inclusive_histogram['*' if op == '*' else '+'] += 1
    assert len(INCLUSIVE_SCHEDULE) == 11 and inclusive_histogram == {'*':5,'+':6}

    neighborhood_tests = 0
    for bits in product(range(2),repeat=9):
        count,center = sum(bits[:8]),bits[8]
        for target,u in product(range(2),auxiliary):
            env = run(dict(**{'n'+str(i):bits[i] for i in range(8)},
                           B=center,Y=target,
                           **{'u'+str(i+1):u[i] for i in range(5)}))
            assert env['lhs']-env['rhs'] == residual(count,center,target,u)
            assert (env['lhs'] == env['rhs']) == (u in solutions[count,center]
                                                and target == life(count,center))
            # The equivalent nonnegative sides give the no-carry proof.
            left = count+22*target+6*(u[0]+u[1])+7*u[2]
            right = 6*center+11*u[3]+14*u[4]
            assert 0 <= left <= 49 < 64 and 0 <= right <= 31 < 64
            assert left-right == env['lhs']-env['rhs']
            inclusive = run(dict(S=count+center,B=center,Y=target,
                                 **{'u'+str(i+1):u[i] for i in range(5)}),
                            INCLUSIVE_SCHEDULE)
            assert inclusive['lhs']-inclusive['rhs'] == env['lhs']-env['rhs']
            assert count+center+22*target+6*(u[0]+u[1])+7*u[2] <= 50 < 64
            assert 7*center+11*u[3]+14*u[4] <= 32 < 64
            neighborhood_tests += 1

    rng = random.Random(20260914)
    packed_checks = 0
    for length in (1,2,3,8,16,31):
        for _ in range(12):
            cells = [tuple(rng.randrange(2) for _ in range(9)) for _ in range(length)]
            targets = [life(sum(bits[:8]),bits[8]) for bits in cells]
            witnesses = [rng.choice(solutions[sum(bits[:8]),bits[8]]) for bits in cells]
            values = {'n'+str(i):pack([bits[i] for bits in cells]) for i in range(8)}
            values.update(B=pack([bits[8] for bits in cells]),Y=pack(targets))
            values.update({'u'+str(i+1):pack([u[i] for u in witnesses]) for i in range(5)})
            env = run(values)
            assert env['lhs'] == env['rhs']
            left = pack([sum(bits[:8])+22*y+6*(u[0]+u[1])+7*u[2]
                         for bits,y,u in zip(cells,targets,witnesses)])
            right = pack([6*bits[8]+11*u[3]+14*u[4]
                          for bits,u in zip(cells,witnesses)])
            assert left == right
            # Deliberately corrupt an output while retaining its witnesses.
            position = rng.randrange(length)
            values['Y'] += (1-2*targets[position])*64**position
            corrupt = run(values)
            assert corrupt['lhs'] != corrupt['rhs']
            packed_checks += 1

    # Radix32 is not sound for this unchanged relation: carries can cancel.
    low = dict(count=2,center=0,target=1,u=(1,1,1,1,0))
    high = dict(count=0,center=0,target=0,u=(0,1,1,0,1))
    low_r = residual(**low)
    high_r = residual(**high)
    assert (low_r,high_r) == (32,-1)
    assert low_r+32*high_r == 0
    assert low['target'] != life(low['count'],low['center'])

    subset_sums = sorted({sum(a*b for a,b in zip((6,6,7,11,14),u)) for u in auxiliary})
    assert subset_sums == [0,6,7,11,12,13,14,17,18,19,20,21,23,24,25,26,27,30,31,32,33,37,38,44]
    return dict(
        status='LIFE_LOCAL_ARITHMETIC_PASS',
        universality_status='NOT_CLAIMED',
        local_operations=18,primitive_histogram=histogram,
        schedule=[dict(name=n,op=o,left=l,right=r) for n,o,l,r in SCHEDULE],
        equality=['lhs','rhs'],radix=64,
        expression='N+22Y+6(U1+U2-B)+7U3=11U4+14U5',
        extra_Boolean_planes=5,
        inclusive_sum_predicate_operations=11,
        inclusive_sum_predicate_histogram=inclusive_histogram,
        inclusive_sum_schedule=[dict(name=n,op=o,left=l,right=r)
                                for n,o,l,r in INCLUSIVE_SCHEDULE],
        inclusive_sum_expression='S+22Y+6(U1+U2)+7(U3-B)=11U4+14U5, S=N+B',
        conditional_separable_aggregation_and_predicate_operations=15,
        mask_fields_with_aligned_neighbors_and_given_Boolean_target=6,
        count_center_output_assignments=36,
        scalar_auxiliary_tests=count_tests,
        full_neighborhood_output_auxiliary_tests=neighborhood_tests,
        deterministic_packed_cases_and_corruptions=packed_checks,
        positive_side_digit_bounds=[49,31],
        subset_sum_set=subset_sums,
        scalar_witness_multiplicities=[dict(count=n,center=b,witnesses=len(solutions[n,b]))
                                      for n,b in product(range(9),range(2))],
        radix32_local_carry_collision=dict(low=low,high=high,residuals=[low_r,high_r]),
        scope='A complete finite local truth-table proof and counted linear packed relation. Neighbor alignment, torus seams, periodic input repetition, Boolean masks and representation of zero auxiliary planes are not paid by these 18 operations. No optimum or universal certificate is claimed.',
        proof_note='../1980/EXPLORATION_LIFE_LOCAL_ARITHMETIC.md')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['local_operations'],result['primitive_histogram'])
    print(result['full_neighborhood_output_auxiliary_tests'],'complete local cases;',
          result['deterministic_packed_cases_and_corruptions'],'packed cases and corruptions')
