"""A 90-operation universal polynomial and smaller-degree product variants.

A shifted positive transport quotient shares q-F. The fully merged case
excludes a negative index unit using the unchanged strong auxiliary kernel.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_norm_product91 as prior


eliminated = prior.eliminated
RETAINED = ['zplus' if name == 'zquot' else name for name in prior.RETAINED]
FACTOR_NAMES = prior.NORM_NAMES+('norm_transport',)
FACTOR_DEGREES = prior.NORM_DEGREES+(5,)
PRODUCT_NAMES = ('norm_pair', 'norm_triple', 'norm_four', 'norm_product', 'all_units')


def ordered(nodes, pairs):
    free = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    certificate, active, done = [], set(), set(free)

    def visit(name):
        if isinstance(name, int) or name in done:
            return
        assert name not in active, ('cyclic definition', name)
        active.add(name)
        op, left, right = nodes[name]
        visit(left)
        visit(right)
        certificate.append((name, op, left, right))
        active.remove(name)
        done.add(name)

    for left, right in pairs:
        visit(left)
        visit(right)
    assert len(certificate) == len(nodes)
    return certificate


def sources():
    original, old, pairs, _ = prior.sources()
    nodes = {name: (op, 'zplus' if left == 'zquot' else left,
                   'zplus' if right == 'zquot' else right)
             for name, op, left, right in old}
    assert nodes.pop('local_rhs_sum') == ('+', 'F', 'local_rhs')
    nodes.update(transport_partial=('+', 'innerC', 'q_minus_F'),
                 norm_transport=('-', 'transport_partial', 'local_rhs'),
                 all_units=('*', 'norm_product', 'norm_transport'))
    comparisons = pairs[1:-1]+[('all_units', 1)]
    assert comparisons[:2] == [('ic22', 'R16'), ('H17', 'aux_u_rhs')]
    certificate = ordered(nodes, comparisons)
    assert len(certificate) == 82 and len(comparisons) == 3 and len(RETAINED) == 19
    return original, certificate, comparisons


def partition_sources(partition):
    assert all(group for group in partition)
    assert sorted(i for group in partition for i in group) == list(range(6))
    original, full, pairs = sources()
    nodes = {name: (op, left, right) for name, op, left, right in full
             if name not in PRODUCT_NAMES}
    comparisons = list(pairs[:-1])
    for group_number, group in enumerate(partition):
        last = FACTOR_NAMES[group[0]]
        for position, factor in enumerate(group[1:], 1):
            name = f'group_{group_number}_{position}'
            nodes[name] = ('*', last, FACTOR_NAMES[factor])
            last = name
        comparisons.append((last, 1))
    certificate = ordered(nodes, comparisons)
    assert len(certificate) == 83-len(partition)
    return original, certificate, comparisons


def source_identity_checks(certificate, pairs, partition, seed, count):
    original, _, _ = sources()
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    rng = random.Random(seed)
    negative_C = negative_R = zero_old_quotient = 0
    for case in range(count):
        supplied = {name: rng.randint(1, 9) for name in RETAINED+['x']}
        supplied['F'] = rng.randint(1, 200)
        if case % 5 == 0:
            supplied['zplus'] = 1
        constants = dict(B=rng.choice((16, 32, 64)), DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    'zquot': supplied['zplus']-1,
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        old = eliminated.run(original, eliminated.fixed_inputs(full))
        residuals = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        factors = (1-residuals[5], 1+residuals[11], 1+residuals[17],
                   1+residuals[13], 1+residuals[8], 1+residuals[2])
        assert [env[name] for name in FACTOR_NAMES] == list(factors)
        assert all(residuals[i] == 0 for i in prior.bounded.DELETED_EQUALITIES)
        assert [env[left]-env[right] for left, right in pairs[:2]] == [residuals[12], residuals[14]]
        expected_polynomial = residuals[12]**2+residuals[14]**2
        for group in partition:
            product = 1
            for index in group:
                product *= factors[index]
            expected_polynomial += (product-1)**2
        assert env[output] == expected_polynomial
        assert env['kinner'] >= env['q']**3 > 1
        negative_C += env['marked_rhs'] < 0
        negative_R += env['r_lhs'] < 0
        zero_old_quotient += restored['zquot'] == 0
    assert negative_C and negative_R and zero_old_quotient
    return dict(original_source_factor_identities=count, full_polynomial_identities=count,
                negative_C_cases=negative_C, negative_R_cases=negative_R,
                zero_old_quotient_cases=zero_old_quotient)


def degree_check(certificate, pairs, partition, B, unequal):
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    t = sp.Symbol('t')
    scales = {name: 1+(j % 3) if unequal else 1 for j, name in enumerate(RETAINED+['x'])}
    fixture = {name: sp.Poly(scale*t, t) for name, scale in scales.items()}
    fixture.update(B=B, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
    env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
    factors = [sp.Poly(env[name], t) for name in FACTOR_NAMES]
    assert [p.degree() for p in factors] == list(FACTOR_DEGREES)
    Ctop = (B-1)*scales['Jrep']-scales['F']-scales['Z']-scales['alpha']-10*scales['x']
    assert factors[-1].LC() == (B-1)**3*scales['w']*scales['Jrep']**3*Ctop
    group_degrees = [sum(FACTOR_DEGREES[i] for i in group) for group in partition]
    maximum = max(group_degrees)
    expected_leading = 0
    for group, degree in zip(partition, group_degrees):
        if degree == maximum:
            coefficient = 1
            for i in group:
                coefficient *= factors[i].LC()
            expected_leading += coefficient**2
    actual = sp.Poly(env[output], t)
    assert actual.degree() == 2*maximum and actual.LC() == expected_leading
    return dict(B=B, unequal_positive_scales=unequal, factor_degrees=list(FACTOR_DEGREES),
                group_degrees=group_degrees, polynomial_degree=actual.degree(),
                leading_coefficient=str(actual.LC()))


def audit_source(certificate, pairs):
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, _, left, right in polynomial:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    poly_counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    return dict(certificate=dict(operations=len(certificate), multiplications=counts['M'],
                                 additions_subtractions=counts['A'], witnesses=19, equations=len(pairs)),
                polynomial=dict(operations=len(polynomial), multiplications=poly_counts['M'],
                                additions_subtractions=poly_counts['A'], witnesses=19,
                                output_register=output),
                comparisons=pairs, polynomial_schedule=polynomial)


def verify_source():
    _, certificate, pairs = sources()
    _, old, _, _ = prior.sources()
    expected = {name: (op, 'zplus' if left == 'zquot' else left,
                       'zplus' if right == 'zquot' else right)
                for name, op, left, right in old if name != 'local_rhs_sum'}
    expected.update(transport_partial=('+', 'innerC', 'q_minus_F'),
                    norm_transport=('-', 'transport_partial', 'local_rhs'),
                    all_units=('*', 'norm_product', 'norm_transport'))
    assert {name: (op, left, right) for name, op, left, right in certificate} == expected
    q, F, z, C, K = sp.symbols('q F z C K')
    assert sp.expand(K*C+q-F-(z+1)*(q-1)-(K*C-F-z*(q-1)+1)) == 0
    result = audit_source(certificate, pairs)
    assert result['certificate'] == dict(operations=82, multiplications=46,
                                         additions_subtractions=36, witnesses=19, equations=3)
    assert result['polynomial']['operations'] == 90
    assert (result['polynomial']['multiplications'], result['polynomial']['additions_subtractions']) == (49, 41)
    result['polynomial']['exact_degree'] = 276
    result['positive_witnesses'] = RETAINED
    result['rewiring'] = dict(preserved_old_gates=79, replaced_old_gate=1,
                              new_transport_additions_subtractions=2, new_product=1,
                              restored_old_quotient='zquot=zplus-1', transport_unit_identity=True)
    partition = ((0, 1, 2, 3, 4, 5),)
    result['identities'] = source_identity_checks(certificate, pairs, partition, 75090, 256)
    result['degree_fixtures'] = [degree_check(certificate, pairs, partition, B, unequal)
                                for B, unequal in ((16, False), (32, True), (64, True))]
    result['highest_homogeneous_term'] = '1024*(B-1)^180*h^2*delta^4*i^4*j^4*w^22*s^38*Jrep^180*(eta+zeta)^18*(rho+sigma)^2*C_top^2'
    result['C_top'] = '(B-1)*Jrep-F-Z-alpha-2*cell_bits*x'
    return result


def verify_partitions():
    partitions = list(prior.set_partitions(list(range(6))))
    assert len(partitions) == 203
    optimum = {}
    for groups in range(1, 7):
        candidates = [p for p in partitions if len(p) == groups]
        best = min(max(sum(FACTOR_DEGREES[i] for i in group) for group in p) for p in candidates)
        optimum[groups] = dict(candidate_partitions=len(candidates), minimum_largest_group_degree=best,
                               optimal_partition_count=sum(max(sum(FACTOR_DEGREES[i] for i in group)
                                                                for group in p) == best for p in candidates))
    assert [optimum[g]['minimum_largest_group_degree'] for g in (6, 5, 4, 3, 2, 1)] == [42, 42, 42, 48, 69, 138]
    selected = (((0,), (1, 4), (2,), (3, 5)),
                ((0, 1), (2, 5), (3, 4)),
                ((0, 3, 4), (1, 2, 5)))
    variants = []
    for partition in selected:
        groups = len(partition)
        assert all(not (4 in group and 5 in group) for group in partition)
        _, certificate, pairs = partition_sources(partition)
        result = audit_source(certificate, pairs)
        assert result['certificate']['operations'] == 83-groups
        assert result['certificate']['multiplications'] == 47-groups
        assert result['certificate']['additions_subtractions'] == 36
        assert result['polynomial']['operations'] == 88+2*groups
        assert result['polynomial']['multiplications'] == 49
        assert result['polynomial']['additions_subtractions'] == 39+2*groups
        result['partition'] = partition
        result['negative_index_exclusion_needed'] = False
        result['identities'] = source_identity_checks(certificate, pairs, partition, 75600+groups, 64)
        result['degree_fixture'] = degree_check(certificate, pairs, partition, 16, False)
        result['polynomial']['exact_degree'] = 2*optimum[groups]['minimum_largest_group_degree']
        variants.append(result)
    return dict(all_set_partitions=203, optimum_by_group_count=optimum, variants=variants,
                scope='Degree optimum only among partitions of these six factors with these literal circuits')


def verify_bootstrap_and_negative_index():
    partial = zero_C = 0
    for q in (16, 31, 32, 46, 64):
        coefficient = q**3+3
        for F in range(1, q+3):
            for zplus in range(1, 5):
                for unit in (-1, 1):
                    numerator = F+(zplus-1)*(q-1)+unit-1
                    assert numerator >= -1
                    if numerator % coefficient:
                        continue
                    C = numerator//coefficient
                    assert C >= 0
                    zero_C += C == 0
                    if C == 0:
                        assert (F, zplus, unit) == (2, 1, -1)
                    partial += 1
    assert zero_C
    pell = prior.bounded.signed.dominance.kernel.binary.pell
    ratio = 0
    for X in (1, 2, 4, 16, 4096):
        for Y in (1, 2, 4, 16, 4096):
            A, P = Y*(X+1)+2, 2*X*Y*Y+1
            Q = 2*A*A-1
            assert Q > P and A > Y+1
            for n in range(1, 10):
                _, first = pell(P, n)
                _, doubled = pell(A, 2*n)
                _, counterpart = pell(Q, n)
                _, main = pell(A, 2*n+1)
                assert doubled == 2*A*counterpart >= 2*A*first
                assert main > 2*first*(Y+1)
                ratio += 1
    X, Y = sp.symbols('X Y')
    A, P = Y*(X+1)+2, 2*X*Y*Y+1
    assert sp.expand(2*A*A-1-P-(2*Y*Y*(X*X+X+1)+8*Y*(X+1)+6)) == 0
    return dict(integer_transport_bootstrap_cases=partial, zero_C_boundary_cases=zero_C,
                exact_negative_index_ratio_cases=ratio, positive_parameter_difference_identity=True,
                scope='Partial arithmetic/Pell interface checks; strong-rank recovery is the cited parametric proof, not these fixtures')


def verify():
    return dict(status='PASS_COMPLETE75_NORM_PRODUCT90', source=verify_source(),
                partitions=verify_partitions(), conditional_index=verify_bootstrap_and_negative_index(),
                inherited_negative_unit_lemmas=prior.verify_negative_unit_lemma(),
                inherited_compiler_margin=prior.bounded.verify_compiler_margin(),
                established_complete_comparison_bound=75,
                theorem='The fixed complete75 compiler has the same ordinary-input language via cost90 degree276 in19 positive witnesses; variants96/84,94/96,92/138 are also certified',
                limits='Main90 needs conditional negative-index exclusion with the unchanged strong auxiliary equations. The three displayed partition variants avoid that lemma. Intermediate signs and zero restored quotient are allowed only in off-zero identity tests.')


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
    print(result['status'], result['source']['certificate'], result['source']['polynomial'])
