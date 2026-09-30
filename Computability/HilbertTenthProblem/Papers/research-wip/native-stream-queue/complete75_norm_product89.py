"""An unsquared eight-factor universal polynomial: 89 operations, degree 166.

The note proves the conditional auxiliary-unit sign exclusion before applying
norm_product90. This checker audits the literal circuit and supporting identities.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_norm_product90 as prior


eliminated = prior.eliminated
RETAINED = prior.RETAINED
FACTOR_NAMES = prior.FACTOR_NAMES + ('norm_strong', 'norm_linear')
FACTOR_DEGREES = prior.FACTOR_DEGREES + (22, 6)


def sources():
    original, old, pairs = prior.sources()
    assert pairs == [('ic22', 'R16'), ('H17', 'aux_u_rhs'), ('all_units', 1)]
    nodes = {name: (op, left, right) for name, op, left, right in old}
    nodes.update(strong_difference=('-', 'ic22', 'R16'),
                 norm_strong=('+', 'strong_difference', 1),
                 linear_difference=('-', 'H17', 'aux_u_rhs'),
                 norm_linear=('+', 'linear_difference', 1),
                 seven_units=('*', 'all_units', 'norm_strong'),
                 eight_units=('*', 'seven_units', 'norm_linear'))
    comparisons = [('eight_units', 1)]
    certificate = prior.ordered(nodes, comparisons)
    assert len(certificate) == 88 and len(RETAINED) == 19
    polynomial = certificate + [('polynomial', '-', 'eight_units', 1)]
    return original, certificate, comparisons, polynomial


def manual_factors(values, constants):
    """Independent mathematical formulas, without source register aliases."""
    v = values
    B, d, b = constants['B'], constants['cell_bits'], constants['inner_bits']
    q = (B-1)*v['Jrep']+1
    X, Y = v['w']*q**3, v['s']*q**3
    E = X*Y
    k = v['eta']+v['zeta']
    a = E+Y
    c = k*Y+v['eta']
    A, H = a+2, 4*a+3
    Delta = A*A-1
    D = X+a*c+(v['rho']+v['sigma'])*H
    C = q-v['F']-v['Z']-v['alpha']-2*d*v['x']
    W = C-v['Z']
    kappa = 2*d*v['x']+b+v['delta']*Delta
    mu = W+a*kappa+v['rho']*H
    G = q*q-v['Z']-q*v['F']
    R = G*(q*q-1)+(constants['MC']+q*(constants['MF']+B-1))*v['Jrep']
    T, U = v['i']*c*c, v['j']*c-R
    K0 = constants['DC']+B*constants['DR']
    return (v['tau']**2-(E*E+X)*(k*Y)**2,
            D*D-Delta*c*c,
            mu*mu-Delta*kappa*kappa,
            T*T*(U*U-v['y_aux']**2)+v['y_aux']**2,
            k-R-v['h']*E,
            (K0+X)*C+q-v['F']-v['zplus']*(q-1),
            1+T*T-Delta*(v['f']**2-1),
            1+U-v['o']*v['f']+c)


def multiply(values):
    result = 1
    for value in values:
        result *= value
    return result


def verify_source():
    original, certificate, comparisons, polynomial = sources()
    _, old, _ = prior.sources()
    old_nodes = {name: (op, left, right) for name, op, left, right in old}
    actual_nodes = {name: (op, left, right) for name, op, left, right in certificate}
    assert all(actual_nodes[name] == node for name, node in old_nodes.items())
    assert len(actual_nodes.keys()-old_nodes.keys()) == 6
    available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, op, left, right in polynomial:
        assert op in ('+', '-', '*') and name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert cc == {'M': 48, 'A': 40} and pc == {'M': 48, 'A': 41}
    rng = random.Random(75089)
    counts = Counter()
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
        factors = manual_factors(supplied, constants)
        assert tuple(env[name] for name in FACTOR_NAMES) == factors
        assert env['polynomial'] == multiply(factors)-1
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    'zquot': supplied['zplus']-1,
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        old_env = eliminated.run(original, eliminated.fixed_inputs(full))
        residuals = [old_env[left]-old_env[right]
                     for left, right in eliminated.baseline.prior.EQUALITIES]
        expected = (1-residuals[5], 1+residuals[11], 1+residuals[17],
                    1+residuals[13], 1+residuals[8], 1+residuals[2],
                    1+residuals[12], 1+residuals[14])
        assert factors == expected
        assert all(residuals[index] == 0 for index in prior.prior.bounded.DELETED_EQUALITIES)
        assert env['polynomial'] == multiply(expected)-1
        counts['signed_supplied_assignments' if signed else 'positive_supplied_assignments'] += 1
        counts['negative_computed_C'] += env['marked_rhs'] < 0
        counts['negative_computed_R'] += env['r_lhs'] < 0
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['zero_restored_old_quotient'] += restored['zquot'] == 0
    assert all(counts[k] > 0 for k in counts)
    return dict(certificate=dict(operations=88, multiplications=48, additions_subtractions=40,
                                 witnesses=19, equations=1),
                polynomial=dict(operations=89, multiplications=48, additions_subtractions=41,
                                witnesses=19, exact_degree=166, output_register='polynomial',
                                unsquared_residual=True),
                positive_witnesses=RETAINED, factor_names=FACTOR_NAMES,
                comparisons=comparisons, polynomial_schedule=polynomial,
                preserved_prior_gates=82, added_certificate_gates=6,
                original19_source_identities=512, independent_formula_identities=512,
                assignment_counts=dict(counts),
                source_identity='(1-r5)(1+r11)(1+r17)(1+r13)(1+r8)(1+r2)(1+r12)(1+r14)-1')


def highest_forms(v, B, d):
    Q = (B-1)*v['Jrep']
    k = v['eta']+v['zeta']
    gamma = v['rho']+v['sigma']
    w, s = v['w'], v['s']
    Ctop = Q-v['F']-v['Z']-v['alpha']-2*d*v['x']
    return (-k*k*w*w*s**4*Q**18,
            8*gamma*k*w*w*s**3*Q**15,
            -4*v['delta']**2*w**5*s**5*Q**30,
            v['i']**2*v['j']**2*k**6*s**6*Q**18,
            -v['h']*w*s*Q**6,
            w*Q**3*Ctop,
            v['i']**2*k**4*s**4*Q**12,
            v['j']*k*s*Q**3)


def verify_degrees():
    _, _, _, polynomial = sources()
    rng = random.Random(89166)
    t = sp.Symbol('t')
    fixtures = []
    for B, d in ((16, 4), (32, 5), (64, 6), (256, 8)):
        scales = {name: rng.randint(1, 7) for name in RETAINED+['x']}
        offsets = {name: rng.randint(0, 7) for name in RETAINED+['x']}
        fixture = {name: sp.Poly(scales[name]*t+offsets[name], t) for name in scales}
        fixture.update(B=B, DC=1, DR=1, MC=1, MF=1, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
        factors = [sp.Poly(env[name], t) for name in FACTOR_NAMES]
        expected = highest_forms(scales, B, d)
        assert all(expected)
        assert tuple(p.degree() for p in factors) == FACTOR_DEGREES
        assert tuple(p.LC() for p in factors) == expected
        output = sp.Poly(env['polynomial'], t)
        Ctop = (B-1)*scales['Jrep']-scales['F']-scales['Z']-scales['alpha']-2*d*scales['x']
        leading = (-32*(B-1)**105*scales['h']*(scales['rho']+scales['sigma'])
                   *scales['delta']**2*scales['i']**4*scales['j']**3
                   *(scales['eta']+scales['zeta'])**14*scales['w']**11
                   *scales['s']**24*scales['Jrep']**105*Ctop)
        assert output.degree() == 166 and output.LC() == multiply(expected) == leading
        fixtures.append(dict(B=B, cell_bits=d, scales=scales, offsets=offsets,
                             factor_degrees=FACTOR_DEGREES, exact_degree=166,
                             leading_coefficient=str(leading)))
    return dict(fixtures=fixtures,
                highest_homogeneous_term='-32*(B-1)^105*h*(rho+sigma)*delta^2*i^4*j^3*(eta+zeta)^14*w^11*s^24*Jrep^105*C_top',
                C_top='(B-1)*Jrep-F-Z-alpha-2*cell_bits*x',
                upper_bound_reason='Inherited six factor degrees plus degree22 strong factor and degree6 linear factor; all highest forms are nonzero')


def pell(A, index):
    """Binary exponentiation in Z[sqrt(A^2-1)], independent of inherited code."""
    Delta = A*A-1
    x, y, bx, by = 1, 0, A, 1
    while index:
        if index & 1:
            x, y = x*bx+Delta*y*by, x*by+y*bx
        bx, by = bx*bx+Delta*by*by, 2*bx*by
        index //= 2
    return x, y


def odd_quotient(argument, h):
    if h == 0:
        return 1
    previous, current = 1, 4*argument-3
    for _ in range(1, h):
        previous, current = current, (4*argument-2)*current-previous
    return current


def verify_sign_and_folding():
    modular = []
    for A in range(4):
        for T in range(4):
            for f in range(4):
                value = (1+T*T-(A*A-1)*(f*f-1)) % 4
                assert value != 3
                modular.append((A, T, f, value))
    signed = 0
    for A in range(-12, 13):
        for T in range(-12, 13):
            for f in range(-12, 13):
                assert 1+T*T-(A*A-1)*(f*f-1) != -1
                signed += 1
    folded = odd = gaps = 0
    for A in range(3, 19):
        Delta = A*A-1
        for m in range(1, 25):
            f, psim = pell(A, m)
            assert 2*psim < f
            for ell in range(6*m+1):
                quotient, r = divmod(ell, 2*m)
                if r > m:
                    r = 2*m-r
                small = (-1)**quotient*pell(A, r)[1]
                assert (pell(A, ell)[1]-small) % f == 0
                assert 2*abs(small) < f
                folded += 1
        for p in range(1, 25):
            c = pell(A, p)[1]
            if c <= 2:
                continue
            f = pell(A, 2*p+1)[0]
            assert 1+2*Delta*c*c == pell(A, 2*p)[0] < f
            assert 2*(c+2) < f
            assert pell(A, p+1)[1] > c+2
            assert all(pell(A, r)[1] != c+2 for r in range(2*p+2))
            gaps += 1
        for m in range(1, 13):
            f, psim = pell(A, m)
            T = Delta*psim
            assert T*T == Delta*(f*f-1)
            for h in range(13):
                ell = 2*h+1
                Q = odd_quotient(T*T, h)
                assert pell(T, ell)[0] == T*Q
                assert odd_quotient(1-A*A, h) == (-1)**h*pell(A, ell)[1]
                assert odd_quotient(0, h) == (-1)**h*ell
                assert (Q-(-1)**h*pell(A, ell)[1]) % f == 0
                odd += 1
    return dict(mod4_residue_cases=len(modular), mod4_table=modular,
                signed_integer_strong_factor_cases=signed,
                folded_residue_cases=folded, odd_index_polynomial_cases=odd,
                strict_gap_cases=gaps,
                scope='Finite exact checks supplement the uniform residue folding and ordered sign proof in the note; they do not test complete accepting witnesses')


def verify():
    return dict(status='PASS_COMPLETE75_NORM_PRODUCT89', source=verify_source(),
                degree=verify_degrees(), unit_and_residue_checks=verify_sign_and_folding(),
                inherited_negative_norm_lemmas=prior.prior.verify_negative_unit_lemma(),
                inherited_weak_transport_and_negative_index=prior.verify_bootstrap_and_negative_index(),
                inherited_compiler_margin=prior.prior.bounded.verify_compiler_margin(),
                established_complete_comparison_bound=75,
                theorem='The same fixed compiler and ordinary positive input have an89-operation polynomial of exactdegree166 with19 strictlypositive witnesses',
                limits='Integer zero-set equivalence uses the new conditional linear-unit exclusion and prior90 negative-index proof; no real-zero equivalence, circuit optimality, or proof-assistant formalization is claimed')


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
