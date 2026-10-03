"""Reverse the auxiliary root and reduce its multiplier: cost89, degree160.

The strong unit restores the square multiplier before Pell classification. Reversing the linear-unit sign makes both extra index branches fail.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_norm_product89 as prior


eliminated = prior.eliminated
RETAINED = prior.RETAINED
FACTOR_NAMES = prior.FACTOR_NAMES
FACTOR_DEGREES = (26, 22, 42, 28, 9, 5, 22, 6)


def sources():
    original, old, comparisons, _ = prior.sources()
    nodes = {name: (op, left, right) for name, op, left, right in old}
    assert nodes['H2'] == ('*', 'H17', 'H17')
    assert nodes['L17'] == ('*', 'ic22', 'aux_square_gap')
    assert nodes['linear_difference'] == ('-', 'H17', 'aux_u_rhs')
    nodes['H2'] = ('*', 'aux_u_rhs', 'aux_u_rhs')
    nodes['L17'] = ('*', 'R16', 'aux_square_gap')
    nodes['linear_difference'] = ('-', 'aux_u_rhs', 'H17')
    certificate = prior.prior.ordered(nodes, comparisons)
    polynomial = certificate + [('polynomial', '-', 'eight_units', 1)]
    return original, certificate, comparisons, polynomial


def manual_factors(v, constants):
    factors = list(prior.manual_factors(v, constants))
    B = constants['B']
    q = (B-1)*v['Jrep']+1
    X, Y = v['w']*q**3, v['s']*q**3
    a = X*Y+Y
    Delta = (a+2)**2-1
    c = (v['eta']+v['zeta'])*Y+v['eta']
    V = v['o']*v['f']-c
    K = Delta*(v['f']**2-1)
    factors[3] = K*(V*V-v['y_aux']**2)+v['y_aux']**2
    factors[7] = 2-factors[7]
    return tuple(factors)


def verify_source():
    original, certificate, comparisons, polynomial = sources()
    _, old, _, _ = prior.sources()
    before = {name: (op, left, right) for name, op, left, right in old}
    after = {name: (op, left, right) for name, op, left, right in certificate}
    assert before.keys() == after.keys()
    assert {name for name in before if before[name] != after[name]} == {'H2', 'L17', 'linear_difference'}
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, op, left, right in polynomial:
        assert op in ('+', '-', '*') and name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    polycounts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert counts == {'M': 48, 'A': 40} and polycounts == {'M': 48, 'A': 41}
    rng = random.Random(89160)
    assignment_counts = Counter()
    for case in range(512):
        signed = case >= 384
        supplied = {name: rng.randint(-9, 9) if signed else rng.randint(1, 9)
                    for name in RETAINED+['x']}
        supplied['F'] = rng.randint(-200, 200) if signed else rng.randint(1, 200)
        if case % 5 == 0:
            supplied['zplus'] = 1
        constants = dict(B=rng.choice((16, 32, 64, 256)), DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        expected = manual_factors(supplied, constants)
        assert tuple(env[name] for name in FACTOR_NAMES) == expected
        assert env['polynomial'] == prior.multiply(expected)-1
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    'zquot': supplied['zplus']-1,
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        old_env = eliminated.run(original, eliminated.fixed_inputs(full))
        residuals = [old_env[left]-old_env[right]
                     for left, right in eliminated.baseline.prior.EQUALITIES]
        U, V, y, T2 = env['H17'], env['aux_u_rhs'], supplied['y_aux'], env['ic22']
        correction = -T2*residuals[14]*(U+V)-residuals[12]*(V*V-y*y)
        source_factors = (1-residuals[5], 1+residuals[11], 1+residuals[17],
                          1+residuals[13]+correction, 1+residuals[8],
                          1+residuals[2], 1+residuals[12], 1-residuals[14])
        assert source_factors == expected
        assert env['polynomial'] == prior.multiply(source_factors)-1
        assert all(residuals[index] == 0 for index in prior.prior.prior.bounded.DELETED_EQUALITIES)
        assignment_counts['signed_supplied_assignments' if signed else 'positive_supplied_assignments'] += 1
        assignment_counts['negative_computed_C'] += env['marked_rhs'] < 0
        assignment_counts['negative_computed_R'] += env['r_lhs'] < 0
        assignment_counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        assignment_counts['zero_restored_old_quotient'] += restored['zquot'] == 0
    assert all(assignment_counts.values())
    U, V, y, T2, K = sp.symbols('U V y T2 K')
    old_aux = T2*(U*U-y*y)+y*y
    new_aux = K*(V*V-y*y)+y*y
    correction = -T2*(U-V)*(U+V)-(T2-K)*(V*V-y*y)
    assert sp.expand(new_aux-old_aux-correction) == 0
    return dict(certificate=dict(operations=88, multiplications=48, additions_subtractions=40,
                                 witnesses=19, equations=1),
                polynomial=dict(operations=89, multiplications=48, additions_subtractions=41,
                                witnesses=19, exact_degree=160, output_register='polynomial',
                                unsquared_residual=True),
                positive_witnesses=RETAINED, comparisons=comparisons,
                polynomial_schedule=polynomial,
                changed_registers=['H2', 'L17', 'linear_difference'],
                original19_source_identities=512, independent_formula_identities=512,
                assignment_counts=dict(assignment_counts), symbolic_auxiliary_correction=True,
                source_factors=['1-r5', '1+r11', '1+r17',
                                '1+r13-T^2*r14*(U+V)-r12*(V^2-y^2)',
                                '1+r8', '1+r2', '1+r12', '1-r14'])


def verify_degrees():
    _, _, _, polynomial = sources()
    rng = random.Random(16089)
    t = sp.Symbol('t')
    fixtures = []
    for B, d in ((16, 4), (32, 5), (64, 6), (256, 8)):
        scales = {name: rng.randint(1, 7) for name in RETAINED+['x']}
        offsets = {name: rng.randint(0, 7) for name in RETAINED+['x']}
        fixture = {name: sp.Poly(scales[name]*t+offsets[name], t) for name in scales}
        fixture.update(B=B, DC=1, DR=1, MC=1, MF=1, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
        factors = [sp.Poly(env[name], t) for name in FACTOR_NAMES]
        expected = list(prior.highest_forms(scales, B, d))
        Q, k = (B-1)*scales['Jrep'], scales['eta']+scales['zeta']
        expected[3] = scales['f']**2*k*k*scales['w']**2*scales['s']**4*Q**18
        expected[7] *= -1
        assert all(expected)
        assert tuple(p.degree() for p in factors) == FACTOR_DEGREES
        assert [p.LC() for p in factors] == expected
        Ctop = Q-scales['F']-scales['Z']-scales['alpha']-2*d*scales['x']
        leading = (32*Q**105*scales['h']*(scales['rho']+scales['sigma'])
                   *scales['delta']**2*scales['i']**2*scales['j']*scales['f']**2
                   *k**10*scales['w']**13*scales['s']**22*Ctop)
        output = sp.Poly(env['polynomial'], t)
        assert output.degree() == 160 and output.LC() == prior.multiply(expected) == leading
        fixtures.append(dict(B=B, cell_bits=d, scales=scales, offsets=offsets,
                             factor_degrees=FACTOR_DEGREES, exact_degree=160,
                             leading_coefficient=str(leading)))
    return dict(fixtures=fixtures,
                highest_homogeneous_term='32*(B-1)^105*h*(rho+sigma)*delta^2*i^2*j*f^2*(eta+zeta)^10*w^13*s^22*Jrep^105*C_top',
                C_top='(B-1)*Jrep-F-Z-alpha-2*cell_bits*x',
                upper_bound_reason='The substituted auxiliary factor has degree28, the reversed linear factor degree6, and all other highest forms remain unchanged')


def verify_sign_branches():
    modified_mod4 = 0
    for A in range(4):
        for f in range(4):
            K = (A*A-1)*(f*f-1)
            assert K % 4 in (0, 1)
            for V in range(4):
                for y in range(4):
                    assert (K*(V*V-y*y)+y*y) % 4 in (0, 1)
                    modified_mod4 += 1
    branches = []
    for linear_sign in (-1, 1):
        for index_sign in (-1, 1):
            difference = 1-linear_sign-index_sign
            accepted = (linear_sign, index_sign) == (1, 1)
            assert (difference == -1) == accepted
            assert accepted or difference in (1, 3)
            branches.append(dict(linear_unit=linear_sign, index_unit=index_sign,
                                 main_minus_twice_first_index=difference,
                                 excluded_by_ratio=not accepted))
    pell = prior.pell
    cases = 0
    for X in (1, 2, 4, 16, 4096):
        for Y in (2, 4, 16, 4096):
            A, P0 = Y*(X+1)+2, 2*X*Y*Y+1
            Q = 2*A*A-1
            assert P0 > A and Q > P0 and A > Y+1
            for n in range(1, 13):
                k = 2*pell(P0, n)[1]
                assert pell(A, 2*n)[1] == 2*A*pell(Q, n)[1] >= A*k
                for extra in (1, 3):
                    assert pell(A, 2*n+extra)[1] > k*(Y+1)
                    cases += 1
    rank_size = 0
    for A in range(3, 15):
        for p in range(2, 20):
            c = pell(A, p)[1]
            for m in (2*p+1, 2*p+2, 3*p):
                f = pell(A, m)[0]
                assert f > 2*c and f-c > 0
                rank_size += 1
    # The bad orientation has a formal kernel sign collision after R -> R+2.
    R, c, j, k, h, E, V = sp.symbols('R c j k h E V')
    U = j*c-R
    assert sp.expand((k-(R+2)-h*E)-(k-R-h*E)) == -2
    assert sp.expand((1+(j*c-(R+2))-V)-(1+U-V)) == -2
    return dict(modified_auxiliary_mod4_cases=modified_mod4, unit_sign_branches=branches, exact_ratio_contradictions=cases,
                positive_substituted_root_size_cases=rank_size,
                wrong_orientation_index_shift_identity=True,
                scope='Finite arithmetic checks supplement the parametric signed-index proof; the orientation collision is a formal kernel statement, not an outer packed-input counterexample')


def verify():
    return dict(status='PASS_COMPLETE75_REVERSED_AUXILIARY89', source=verify_source(),
                degree=verify_degrees(), sign_branches=verify_sign_branches(),
                inherited_mod4_and_odd_index_checks=prior.verify_sign_and_folding(),
                inherited_negative_norm_checks=prior.prior.prior.verify_negative_unit_lemma(),
                established_complete_comparison_bound=75,
                theorem='The fixed complete75 compiler has the same ordinary-input language via89 operations and exactdegree160 in19 strictlypositive witnesses',
                limits='Strong-unit positivity precedes auxiliary Pell classification. Reversed linear-unit sign is essential. No real-zero equivalence, global optimum or proof-assistant formalization is claimed')


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
