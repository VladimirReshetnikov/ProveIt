"""A 91-operation universal polynomial using four norms and an affine unit.

Integer negative-Pell obstructions for A^2-1 and V(V+1) make this conjunction
exact. Comparison cost80 and degree266 are explicit tradeoffs.
"""
import argparse
from collections import Counter
from itertools import product
import json
from math import isqrt
from pathlib import Path
import random

import sympy as sp

import complete75_bounded_projection_elimination99 as bounded


eliminated = bounded.eliminated
RETAINED = bounded.RETAINED
NORM_INDICES = {5, 8, 11, 13, 17}


def sources():
    original, prior, pairs, indices = bounded.sources()
    nodes = {name: (op, left, right) for name, op, left, right in prior}
    assert nodes.pop('R9') == ('-', 'tau_square', 1)
    assert nodes.pop('R15') == ('+', 'Ac2', 1)
    assert nodes.pop('norm_rhs') == ('+', 'scaled_kappa2', 1)
    assert nodes.pop('P17') == ('-', 1, 'aux_y2')
    assert nodes.pop('r1') == ('+', 'r_lhs', 1)
    assert nodes.pop('R11') == ('+', 'r1', 'hpm1')
    nodes.update(norm_first=('-', 'tau_square', 'L9'),
                 norm_main=('-', 'L15', 'Ac2'),
                 norm_input=('-', 'mu2', 'scaled_kappa2'),
                 norm_aux=('+', 'L17', 'aux_y2'),
                 index_difference=('-', 'R10b', 'r_lhs'),
                 norm_index=('-', 'index_difference', 'hpm1'),
                 norm_pair=('*', 'norm_first', 'norm_main'),
                 norm_triple=('*', 'norm_pair', 'norm_input'),
                 norm_four=('*', 'norm_triple', 'norm_aux'),
                 norm_product=('*', 'norm_four', 'norm_index'))
    free = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    certificate = []
    active, done = set(), set(free)

    def visit(name):
        if isinstance(name, int) or name in done:
            return name
        assert name not in active, ('cyclic definition', name)
        active.add(name)
        op, left, right = nodes[name]
        left, right = visit(left), visit(right)
        certificate.append((name, op, left, right))
        active.remove(name)
        done.add(name)
        return name

    comparisons, retained_indices = [], []
    for pair, index in zip(pairs, indices):
        if index not in NORM_INDICES:
            comparisons.append(tuple(visit(name) for name in pair))
            retained_indices.append(index)
    comparisons.append((visit('norm_product'), 1))
    retained_indices.append('four_norms_and_affine_unit')
    assert len(certificate) == len(nodes) == 80
    assert len(comparisons) == 4 and len(RETAINED) == 19
    return original, certificate, comparisons, retained_indices


def value(env, name):
    return name if isinstance(name, int) else env[name]


NORM_NAMES = ('norm_first', 'norm_main', 'norm_input', 'norm_aux', 'norm_index')
NORM_DEGREES = (26, 22, 42, 34, 9)


def partition_sources(partition):
    """Group the same four norms and affine unit into separately compared unit products."""
    assert all(group for group in partition)
    assert sorted(index for group in partition for index in group) == list(range(5))
    original, full, pairs, _ = sources()
    nodes = {name: (op, left, right) for name, op, left, right in full
             if name not in ('norm_pair', 'norm_triple', 'norm_four', 'norm_product')}
    comparisons = list(pairs[:-1])
    for group_index, group in enumerate(partition):
        last = NORM_NAMES[group[0]]
        for factor_index, norm_index in enumerate(group[1:], 1):
            name = f'norm_group_{group_index}_{factor_index}'
            nodes[name] = ('*', last, NORM_NAMES[norm_index])
            last = name
        comparisons.append((last, 1))
    free = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    certificate, active, done = [], set(), set(free)

    def visit(name):
        if isinstance(name, int) or name in done:
            return
        assert name not in active
        active.add(name)
        op, left, right = nodes[name]
        visit(left)
        visit(right)
        certificate.append((name, op, left, right))
        active.remove(name)
        done.add(name)

    for left, right in comparisons:
        visit(left)
        visit(right)
    assert len(certificate) == len(nodes) == 81-len(partition)
    return original, certificate, comparisons


def set_partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for partition in set_partitions(rest):
        yield ((first,),)+partition
        for j in range(len(partition)):
            yield partition[:j]+((first,)+partition[j],)+partition[j+1:]


def verify_partition_frontier():
    all_partitions = list(set_partitions(list(range(5))))
    assert len(all_partitions) == 52
    optimal = {}
    for groups in range(1, 6):
        candidates = [p for p in all_partitions if len(p) == groups]
        best = min(max(sum(NORM_DEGREES[i] for i in group) for group in p)
                   for p in candidates)
        winners = [p for p in candidates
                   if max(sum(NORM_DEGREES[i] for i in group) for group in p) == best]
        assert len(winners) == (2 if groups == 4 else 1)
        optimal[groups] = dict(partitions=winners, group_degree=best,
                               polynomial_degree=2*best,
                               candidate_partitions=len(candidates))
    assert [optimal[k]['polynomial_degree'] for k in (5, 4, 3, 2, 1)] == [84, 84, 96, 136, 266]
    variants = []
    rng = random.Random(75097)
    for partition in (((0,), (1,), (2,), (3,), (4,)),
                      ((0,), (1, 4), (2,), (3,)),
                      ((0, 1), (2,), (3, 4)),
                      ((0, 2), (1, 3, 4))):
        groups = len(partition)
        _, certificate, pairs = partition_sources(partition)
        polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
        assert Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate) == {'M': 46-groups, 'A': 35}
        assert Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial) == {'M': 49, 'A': 40+2*groups}
        assert len(polynomial) == 89+2*groups and len(pairs) == 3+groups
        available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
        available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
        for name, _, left, right in polynomial:
            assert name not in available
            assert all(isinstance(v, int) or v in available for v in (left, right))
            available.add(name)
        for _ in range(64):
            supplied = {name: rng.randint(1, 12) for name in RETAINED+['x']}
            constants = dict(B=rng.choice((16, 32, 64)), DC=3, DR=5, MC=10, MF=12,
                             cell_bits=5, inner_bits=3)
            env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
            expected = sum((value(env, left)-value(env, right))**2 for left, right in pairs[:3])
            for group in partition:
                norm_product = 1
                for i in group:
                    norm_product *= env[NORM_NAMES[i]]
                expected += (norm_product-1)**2
            assert env[output] == expected
        t = sp.Symbol('t')
        fixture = {name: sp.Poly(t, t) for name in RETAINED+['x']}
        fixture.update(B=16, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
        norm_polys = [sp.Poly(env[name], t) for name in NORM_NAMES]
        group_degrees = [sum(NORM_DEGREES[i] for i in group) for group in partition]
        largest = max(group_degrees)
        leading = 0
        for group, degree in zip(partition, group_degrees):
            if degree == largest:
                coefficient = 1
                for i in group:
                    coefficient *= norm_polys[i].LC()
                leading += coefficient**2
        actual = sp.Poly(env[output], t)
        assert actual.degree() == 2*largest == optimal[groups]['polynomial_degree']
        assert actual.LC() == leading
        variants.append(dict(partition=partition,
                             certificate=dict(operations=81-groups, multiplications=46-groups,
                                              additions_subtractions=35, equations=3+groups, witnesses=19),
                             polynomial=dict(operations=89+2*groups, multiplications=49,
                                             additions_subtractions=40+2*groups, exact_degree=2*largest,
                                             witnesses=19, output_register=output),
                             comparisons=pairs, polynomial_schedule=polynomial,
                             arbitrary_assignment_identities=64,
                             degree_fixture_leading_coefficient=str(actual.LC())))
    return dict(variants=variants, all_set_partitions=52, optimum_by_group_count=optimal,
                scope='Exact degree minimum only among partitions of these four norms and affine unit with the stated literal product-and-squares schedules')


def verify_source():
    original, certificate, pairs, indices = sources()
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    assert Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate) == {'M': 45, 'A': 35}
    assert Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial) == {'M': 49, 'A': 42}
    assert len(polynomial) == 91
    _, prior, oldpairs, oldindices = bounded.sources()
    expected = {name: (op, left, right) for name, op, left, right in prior
                if name not in ('R9', 'R15', 'norm_rhs', 'P17', 'r1', 'R11')}
    expected.update(norm_first=('-', 'tau_square', 'L9'),
                    norm_main=('-', 'L15', 'Ac2'),
                    norm_input=('-', 'mu2', 'scaled_kappa2'),
                    norm_aux=('+', 'L17', 'aux_y2'),
                    index_difference=('-', 'R10b', 'r_lhs'),
                    norm_index=('-', 'index_difference', 'hpm1'),
                    norm_pair=('*', 'norm_first', 'norm_main'),
                    norm_triple=('*', 'norm_pair', 'norm_input'),
                    norm_four=('*', 'norm_triple', 'norm_aux'),
                    norm_product=('*', 'norm_four', 'norm_index'))
    assert {name: (op, left, right) for name, op, left, right in certificate} == expected
    assert list(zip(indices[:-1], pairs[:-1])) == [
        (index, pair) for index, pair in zip(oldindices, oldpairs) if index not in NORM_INDICES]
    assert pairs[-1] == ('norm_product', 1)
    available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, _, left, right in polynomial:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert not {'R9', 'R15', 'norm_rhs', 'P17', 'r1', 'R11'} & available

    rng = random.Random(75091)
    negative_C = negative_R = 0
    for _ in range(256):
        supplied = {name: rng.randint(1, 9) for name in RETAINED+['x']}
        supplied['F'] = rng.randint(1, 200)
        constants = dict(B=rng.choice((16, 32, 64)), DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        old = eliminated.run(original, eliminated.fixed_inputs(full))
        residuals = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        assert all(residuals[index] == 0 for index in bounded.DELETED_EQUALITIES)
        assert env['norm_first'] == 1-residuals[5]
        assert env['norm_main'] == 1+residuals[11]
        assert env['norm_input'] == 1+residuals[17]
        assert env['norm_aux'] == 1+residuals[13]
        assert env['norm_index'] == 1+residuals[8]
        assert [value(env, left)-value(env, right) for left, right in pairs[:-1]] == [
            residuals[index] for index in indices[:-1]]
        combined = (1-residuals[5])*(1+residuals[11])*(1+residuals[17])*(1+residuals[13])*(1+residuals[8])-1
        assert value(env, pairs[-1][0])-1 == combined
        expected_polynomial = sum(residuals[index]**2 for index in indices[:-1])+combined**2
        assert env[output] == expected_polynomial
        X, Y, k = env['wn2'], env['sn2'], env['R10b']
        V = X*Y*Y
        assert env['norm_first'] == supplied['tau']**2-V*(V+1)*k*k
        A = env['R12']+2
        assert env['A'] == A*A-1 and A >= 2
        # In particular this identity does not assume positive computed mu.
        assert env['norm_input'] == restored['mu']**2-(A*A-1)*restored['kappa']**2
        assert env['norm_main'] == restored['d']**2-(A*A-1)*restored['c']**2
        T, U = env['ic2'], env['H17']
        assert T > 1
        assert env['norm_aux'] == (T*U)**2-(T*T-1)*supplied['y_aux']**2
        negative_C += restored['C'] < 0
        negative_R += restored['r'] < 0
    assert negative_C and negative_R

    t = sp.Symbol('t')
    degree_fixtures = []
    for B, unequal in ((16, False), (32, True), (64, True)):
        scales = {name: (1+(j % 3) if unequal else 1)
                  for j, name in enumerate(RETAINED+['x'])}
        fixture = {name: sp.Poly(scale*t, t) for name, scale in scales.items()}
        fixture.update(B=B, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
        norms = [sp.Poly(env[name], t) for name in ('norm_first', 'norm_main', 'norm_input', 'norm_aux', 'norm_index')]
        assert [p.degree() for p in norms] == [26, 22, 42, 34, 9]
        J, w, s = scales['Jrep'], scales['w'], scales['s']
        k, gamma, delta = scales['eta']+scales['zeta'], scales['rho']+scales['sigma'], scales['delta']
        leading = [-(B-1)**18*w*w*s**4*J**18*k*k,
                   8*(B-1)**15*w*w*s**3*J**15*k*gamma,
                   -4*(B-1)**30*delta*delta*w**5*s**5*J**30,
                   (B-1)**18*scales['i']**2*scales['j']**2*s**6*J**18*k**6,
                   -(B-1)**6*scales['h']*w*s*J**6]
        assert [p.LC() for p in norms] == leading
        degrees = [sp.Poly(env[f'residual_{j}'], t).degree() for j in range(4)]
        assert degrees == [5, 22, 6, 133]
        expression = sp.Poly(env[output], t)
        assert expression.degree() == 266
        assert expression.LC() == (leading[0]*leading[1]*leading[2]*leading[3]*leading[4])**2
        degree_fixtures.append(dict(B=B, unequal_positive_scales=unequal,
                                    norm_degrees=[26, 22, 42, 34, 9], residual_degrees=degrees,
                                    polynomial_degree=266,
                                    leading_coefficient=str(expression.LC())))
    return dict(certificate=dict(operations=80, multiplications=45,
                                 additions_subtractions=35, witnesses=19, equations=4),
                polynomial=dict(operations=91, multiplications=49,
                                additions_subtractions=42, witnesses=19, exact_degree=266,
                                output_register=output),
                positive_witnesses=RETAINED,
                original_comparison_indices_and_combination=indices,
                comparisons=pairs, polynomial_schedule=polynomial,
                original_source_algebraic_replays=256,
                negative_computed_C_identity_cases=negative_C,
                negative_computed_R_identity_cases=negative_R,
                local_symbolic_rewiring=dict(unchanged_gates=70, replaced_gates=6,
                                             new_norm_additions_subtractions=4, new_index_subtractions=2, new_products=4),
                residual_degree_bounds=[5, 22, 6, 133],
                degree_fixtures=degree_fixtures,
                highest_homogeneous_term='1024*(B-1)^174*h^2*delta^4*i^4*j^4*w^20*s^38*Jrep^174*(eta+zeta)^18*(rho+sigma)^2')


def verify_negative_unit_lemma():
    A, x, y = sp.symbols('A x y')
    Delta = A*A-1
    xp, yp = A*x-Delta*y, A*y-x
    assert sp.expand(xp*xp-Delta*yp*yp-(x*x-Delta*y*y)) == 0
    assert sp.expand((Delta*y*y-1)-(A-1)**2*y*y-((2*A-2)*y*y-1)) == 0
    assert sp.expand(A*A*y*y-(Delta*y*y-1)-(y*y+1)) == 0
    V = sp.Symbol('V')
    Delta0 = V*(V+1)
    xx, yy = (2*V+1)*x-2*Delta0*y, (2*V+1)*y-2*x
    assert sp.expand(xx*xx-Delta0*yy*yy-(x*x-Delta0*y*y)) == 0
    assert sp.expand(Delta0*y*y-1-V*V*y*y-(V*y*y-1)) == 0
    assert sp.expand((2*V+1)**2*y*y-4*(Delta0*y*y-1)-(y*y+4)) == 0
    # No finite test can instantiate the impossible descent premise. These
    # exact root searches are independent corroboration, not the proof.
    searched = first_searched = 0
    for a in range(2, 102):
        d = a*a-1
        for yy in range(1, 301):
            candidate = d*yy*yy-1
            root = isqrt(candidate)
            assert root*root != candidate
            searched += 1
            first_candidate = a*(a+1)*yy*yy-1
            first_root = isqrt(first_candidate)
            assert first_root*first_root != first_candidate
            first_searched += 1
    unit_cases = admissible = 0
    for first, main, input_, aux, index in product(range(-3, 4), repeat=5):
        if first*main*input_*aux*index == 1:
            assert all(abs(n) == 1 for n in (first, main, input_, aux, index))
            unit_cases += 1
            if first != -1 and main != -1 and input_ != -1 and aux != -1:
                assert (first, main, input_, aux, index) == (1, 1, 1, 1, 1)
                admissible += 1
    assert unit_cases == 16 and admissible == 1
    return dict(exact_descent_identity=True, exact_descent_interval_identities=True,
                exact_first_norm_descent_and_interval_identities=True,
                signed_root_scope='Both root and coefficient may be signed; absolute values reduce to x,y>0, while y=0 is immediately impossible',
                finite_square_root_search_cases=searched,
                first_norm_square_root_search_cases=first_searched,
                integer_unit_sign_cases=unit_cases, admissible_unit_cases=admissible,
                first_norm_negative_unit_exclusion_needed=True,
                scope='Parametric integer descent proves the lemma; finite searches only corroborate it')


def verify():
    return dict(status='PASS_COMPLETE75_NORM_PRODUCT91',
                source=verify_source(), negative_unit_lemma=verify_negative_unit_lemma(),
                partition_frontier=verify_partition_frontier(),
                inherited_compiler_margin=bounded.verify_compiler_margin(),
                established_complete_comparison_bound=75,
                theorem='The fixed complete75 compiler has the same accepted ordinary inputs via a degree266 polynomial of cost91 in19 positive witnesses',
                limits='Certificate cost80 and degree266 are tradeoffs against99/84 and101/84. The norm product is equivalent on the positive integer witness domain, not a polynomial identity replacing the old sum of squares. The full strong auxiliary norm equation remains unchanged; the auxiliary minus-unit equation is merged equivalently.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'], result['source']['certificate'], result['source']['polynomial'])
