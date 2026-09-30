"""A coupled index/linear unit and compiler packing give88=47M+41A.

Positive zero-set equivalence uses the complete compiler mask hypotheses,
not merely bounds on arbitrary numerical constants. The degree is151.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_positive_root89 as prior

eliminated = prior.eliminated
RETAINED = prior.RETAINED
FACTOR_NAMES = prior.prior.FACTOR_NAMES
FACTOR_DEGREES = (14, 22, 42, 28, 9, 5, 22, 9)


def sources():
    original, old, pairs, _ = prior.sources()
    nodes = {name: (op, left, right) for name, op, left, right in old}
    assert nodes.pop('H17') == ('-', 'jc', 'r_lhs')
    assert nodes['index_difference'] == ('-', 'R10b', 'r_lhs')
    assert nodes['norm_index'] == ('-', 'index_difference', 'hpm1')
    assert nodes['linear_difference'] == ('-', 'aux_u_rhs', 'H17')
    assert nodes['norm_linear'] == ('+', 'linear_difference', 1)
    nodes['index_difference'] = ('-', 'R10b', 'hpm1')
    nodes['norm_index'] = ('-', 'index_difference', 'r_lhs')
    nodes['linear_difference'] = ('-', 'aux_u_rhs', 'jc')
    nodes['norm_linear'] = ('+', 'linear_difference', 'index_difference')
    free = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    active, done, certificate = set(), set(free), []

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

    for left, right in pairs:
        visit(left)
        visit(right)
    assert len(certificate) == len(nodes) == 87
    return original, certificate, pairs, certificate+[('polynomial', '-', 'eight_units', 1)]


def verify_source():
    original, certificate, pairs, polynomial = sources()
    _, old_certificate, oldpairs, old_polynomial = prior.sources()
    assert pairs == oldpairs == [('eight_units', 1)]
    old_nodes = {name: (op, left, right) for name, op, left, right in old_certificate}
    new_nodes = {name: (op, left, right) for name, op, left, right in certificate}
    assert old_nodes.keys()-new_nodes.keys() == {'H17'}
    assert not new_nodes.keys()-old_nodes.keys()
    changed = {name for name in new_nodes if new_nodes[name] != old_nodes[name]}
    assert changed == {'index_difference', 'norm_index', 'linear_difference', 'norm_linear'}
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, op, left, right in polynomial:
        assert name not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert cc == {'M':47, 'A':40} and pc == {'M':47, 'A':41}
    rng, counts = random.Random(88151), Counter()
    for case in range(512):
        signed = case >= 384
        supplied = {name: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
                    for name in RETAINED+['x']}
        supplied['F'] = rng.randrange(-200, 201) if signed else rng.randrange(1, 200)
        if case % 5 == 0:
            supplied['zplus'] = 1
        B = rng.choice((16, 32, 64, 256))
        constants = dict(B=B, DC=3, DR=5, MC=B-2, MF=4,
                         cell_bits=B.bit_length()-1, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        if case < 4:
            supplied['F'] += 2*abs(env['exponent_rhs'])+1
            env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        old = eliminated.run(old_polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        assert all(env[name] == old[name] for name in FACTOR_NAMES[:-1])
        assert env['norm_linear'] == old['norm_linear']+old['norm_index']-1
        assert env['polynomial'] == old['polynomial']+old['seven_units']*(old['norm_index']-1)
        q = (B-1)*supplied['Jrep']+1
        X, Y = supplied['w']*q**3, supplied['s']*q**3
        k = supplied['eta']+supplied['zeta']
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'tau': X*Y*Y*k+supplied['tau_gap'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    'zquot': supplied['zplus']-1,
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        baseline = eliminated.run(original, eliminated.fixed_inputs(full))
        r = [baseline[left]-baseline[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        U = supplied['j']*env['R10a']-env['r_lhs']
        V, T2, y2 = env['aux_u_rhs'], env['ic22'], supplied['y_aux']**2
        factors = (1-r[5], 1+r[11], 1+r[17],
                   1+r[13]-T2*r[14]*(U+V)-r[12]*(V*V-y2),
                   1+r[8], 1+r[2], 1+r[12], 1+r[8]-r[14])
        product = 1
        for factor in factors:
            product *= factor
        assert [env[name] for name in FACTOR_NAMES] == list(factors)
        assert env['polynomial'] == product-1
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['zero_restored_quotient'] += restored['zquot'] == 0
    return dict(certificate=dict(operations=87, multiplications=47, additions_subtractions=40,
                                 equations=1, witnesses=19),
                polynomial=dict(operations=88, multiplications=47, additions_subtractions=41,
                                exact_degree=151, witnesses=19, output_register='polynomial'),
                retained_positive_witnesses=RETAINED, comparisons=pairs,
                polynomial_schedule=polynomial, removed_register='H17',
                changed_registers=sorted(changed), unchanged_gates=83,
                exact_parent_polynomial_correction_cases=512, original19_polynomial_identities=512,
                assignment_counts=dict(counts))


def verify_degree():
    polynomial = sources()[3]
    t, records = sp.Symbol('t'), []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        s = {name: 1+(index+shift) % 4 for index, name in enumerate(RETAINED+['x'])}
        inputs = {name: sp.Poly(s[name]*t+index+1, t) for index, name in enumerate(RETAINED+['x'])}
        inputs.update(B=B, DC=3, DR=5, MC=B-2, MF=4, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(inputs))
        factors = [sp.Poly(env[name], t) for name in FACTOR_NAMES]
        assert tuple(factor.degree() for factor in factors) == FACTOR_DEGREES
        k = s['eta']+s['zeta']
        Q = (B-1)*s['Jrep']
        assert factors[-1].LC() == -s['h']*s['w']*s['s']*Q**6
        Ctop = Q-s['F']-s['Z']-s['alpha']-2*d*s['x']
        top = (-32*Q**99*s['h']**2*(s['rho']+s['sigma'])*s['delta']**2*s['i']**2
               *s['f']**2*k**8*s['w']**13*s['s']**20*Ctop*(2*s['tau_gap']-k))
        actual = sp.Poly(env['polynomial'], t)
        assert actual.degree() == 151 and actual.LC() == top
        records.append(dict(B=B, cell_bits=d, scales=s, factor_degrees=FACTOR_DEGREES,
                            exact_degree=151, leading_coefficient=str(top)))
    return dict(fixtures=records,
                highest_homogeneous_term='-32*(B-1)^99*h^2*(rho+sigma)*delta^2*i^2*f^2*(eta+zeta)^8*w^13*s^20*Jrep^99*C_top*(2*tau_gap-eta-zeta)',
                C_top='(B-1)*Jrep-F-Z-alpha-2*cell_bits*x')


def pell(A, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = A*x+(A*A-1)*y, x+A*y
    return x, y


def verify_signs():
    R, k, h, E, V, j, c = sp.symbols('R k h E V j c')
    Nk, old = k-R-h*E, 1+V-j*c+R
    new = V-j*c+k-h*E
    assert sp.expand(new-old-Nk+1) == 0
    branches = []
    for epsilon in (-1, 1):
        for lam in (-1, 1):
            target_shift = epsilon-lam
            difference = target_shift-epsilon
            assert difference == -lam
            branches.append(dict(index_sign=epsilon, coupled_linear_sign=lam,
                                 main_index_minus_R=target_shift, main_minus_twice_first=difference,
                                 ratio_excludes=lam == -1,
                                 packing_excludes=lam == 1 and epsilon == -1))
    comparisons = 0
    for X in (1, 2, 4, 16, 4096):
        for Y in (2, 4, 16, 4096):
            A, P = Y*(X+1)+2, 2*X*Y*Y+1
            Q = 2*A*A-1
            assert Q > P > A and A > Y+1
            for n in range(1, 13):
                k = 2*pell(P, n)[1]
                assert pell(A, 2*n)[1] == 2*A*pell(Q, n)[1] >= A*k
                assert pell(A, 2*n+1)[1] > k*(Y+1)
                comparisons += 1
    return dict(symbolic_coupled_unit_identity=True, branches=branches,
                exact_ratio_comparisons=comparisons)


def verify_packing():
    rng, counts = random.Random(88301), Counter()
    for d in range(4, 9):
        B = 1 << d
        masks = [(MC, MF) for MC in range(2, B-1, 4) for MF in range(4, B-1, 8)
                 if MC.bit_count()+MF.bit_count() == d]
        assert masks
        if len(masks) > 16:
            masks = [masks[i] for i in sorted(rng.sample(range(len(masks)), 16))]
        for MC, MF in masks:
            for N in (1, 2, 3):
                q, t = B**N, d*N
                J, L = (q-1)//(B-1), q*q
                low, high = MC*J, MF*J
                assert low % 4 == 2 and high % 8 == 4
                shifted = low-1+q*(high-1)
                assert 0 < shifted < L-1
                assert shifted.bit_count() == t+1
                assert (shifted+2).bit_count() == t+2
                assert (2*q-1)*(q*q-1)-2 >= 3*q+1
                assert q**6 > 2*(q**4+2)
                choices = range(1, L) if L <= 1024 else [rng.randrange(1, L) for _ in range(256)]
                for S in choices:
                    p = (L-S)*(L-1)+shifted
                    assert p.bit_count() <= 3*t+1 < 3*t+2
                    counts['inverse_packing_bounds'] += 1
                # F=4,Z=1 gives S'=4q, disjoint from T'-2; the bad bound is sharp.
                S = 4*q
                assert (S & shifted) == 0 and S < L
                p = (L-S)*(L-1)+shifted
                assert p.bit_count() == 3*t+1
                counts['sharp_missing_one_bit_fixtures'] += 1
                counts['mask_power_fixtures'] += 1
    return dict(counts=counts,
                formula='p=(q^2-Sprime)*(q^2-1)+(MC*J-1)+q*(MF*J-1)',
                upper_population='3*t+1', kernel_required_population='3*t+2',
                scope='Finite exact audits supplement the inverse-packing lemma and compiler-mask proof; no complete universal tuple is materialized')


def verify():
    return dict(status='PASS_COMPLETE75_COUPLED_INDEX_LINEAR88', source=verify_source(),
                degree=verify_degree(), signs=verify_signs(), packing=verify_packing(),
                fixed_hypotheses=['B=2^d, d>=4', '0<MC,MF<B-1', 'MC=2 mod4', 'MF=4 mod8',
                                  'popcount(MC)+popcount(MF)=d', 'All remaining complete75 compiler hypotheses'],
                established_complete_comparison_bound=75,
                limits='Positive zero-set equivalence uses the full fixed compiler masks. '
                       'This is not a polynomial identity with the parent at arbitrary assignments. '
                       'Both ratio slacks, the strong auxiliary square and ordinary-input constraints remain.')


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
    print(result['status'], result['source']['polynomial'])
