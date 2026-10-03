"""A positive first-Pell-root coordinate gives89=47M+42A at degree148.

The old root is reconstructed in the proof, not as an extra circuit output.
All ratio slacks and every other strong-kernel factor are retained.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_reversed_auxiliary89 as prior


eliminated = prior.eliminated
RETAINED = ['tau_gap' if name == 'tau' else name for name in prior.RETAINED]
FACTOR_DEGREES = (14, 22, 42, 28, 9, 5, 22, 6)


def sources():
    original, old, pairs, _ = prior.sources()
    nodes = {name: (op, 'tau_gap' if left == 'tau' else left,
                   'tau_gap' if right == 'tau' else right)
             for name, op, left, right in old}
    removed = {name: nodes.pop(name) for name in
               ('UM2', 'scaled_norm_coefficient', 'ratio_product2', 'L9')}
    assert removed == {'UM2': ('*', 'UM', 'UM'),
                       'scaled_norm_coefficient': ('+', 'UM2', 'wn2'),
                       'ratio_product2': ('*', 'ksn2', 'ksn2'),
                       'L9': ('*', 'scaled_norm_coefficient', 'ratio_product2')}
    assert nodes['norm_first'] == ('-', 'tau_square', 'L9')
    nodes.update(first_root_base=('*', 'UM', 'ksn2'),
                 twice_tau_gap=('+', 'tau_gap', 'tau_gap'),
                 first_signed_gap=('-', 'twice_tau_gap', 'R10b'),
                 first_cross=('*', 'first_root_base', 'first_signed_gap'),
                 norm_first=('+', 'tau_square', 'first_cross'))
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
    assert len(certificate) == len(nodes) == 88
    return original, certificate, pairs, certificate+[('polynomial', '-', 'eight_units', 1)]


def verify_source():
    original, certificate, pairs, polynomial = sources()
    _, old_certificate, oldpairs, old_polynomial = prior.sources()
    assert pairs == oldpairs == [('eight_units', 1)]
    old_nodes = {name: (op, 'tau_gap' if left == 'tau' else left,
                      'tau_gap' if right == 'tau' else right)
                 for name, op, left, right in old_certificate}
    new_nodes = {name: (op, left, right) for name, op, left, right in certificate}
    common = old_nodes.keys() & new_nodes.keys()
    assert {name for name in common if old_nodes[name] != new_nodes[name]} == {'norm_first'}
    assert len(common) == 84
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, op, left, right in polynomial:
        assert name not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert cc == {'M':47, 'A':41} and pc == {'M':47, 'A':42}
    rng = random.Random(89148)
    counts = Counter()
    for case in range(512):
        signed = case >= 384
        supplied = {name: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
                    for name in RETAINED+['x']}
        supplied['F'] = rng.randrange(-200, 201) if signed else rng.randrange(1, 200)
        if case % 5 == 0:
            supplied['zplus'] = 1
        constants = dict(B=rng.choice((16, 32, 64, 256)), DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        inputs = {**supplied, **constants}
        env = eliminated.run(polynomial, eliminated.fixed_inputs(inputs))
        q = (constants['B']-1)*supplied['Jrep']+1
        X, Y = supplied['w']*q**3, supplied['s']*q**3
        k = supplied['eta']+supplied['zeta']
        root = X*Y*Y*k+supplied['tau_gap']
        old_inputs = {**inputs, 'tau': root}
        old = eliminated.run(old_polynomial, eliminated.fixed_inputs(old_inputs))
        assert env['polynomial'] == old['polynomial']
        assert all(env[name] == old[name] for name in prior.FACTOR_NAMES)
        assert env['norm_first'] == supplied['tau_gap']**2+X*Y*Y*k*(2*supplied['tau_gap']-k)
        if not signed:
            assert root > 0 and env['first_root_base'] > 0
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'], 'tau': root,
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    'zquot': supplied['zplus']-1,
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**inputs, **restored,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        baseline = eliminated.run(original, eliminated.fixed_inputs(full))
        r = [baseline[left]-baseline[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        U, V, T2, y2 = env['H17'], env['aux_u_rhs'], env['ic22'], supplied['y_aux']**2
        factors = (1-r[5], 1+r[11], 1+r[17],
                   1+r[13]-T2*r[14]*(U+V)-r[12]*(V*V-y2),
                   1+r[8], 1+r[2], 1+r[12], 1-r[14])
        product = 1
        for factor in factors:
            product *= factor
        assert env['polynomial'] == product-1
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['zero_restored_quotient'] += restored['zquot'] == 0
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
    return dict(certificate=dict(operations=88, multiplications=47, additions_subtractions=41,
                                 equations=1, witnesses=19),
                polynomial=dict(operations=89, multiplications=47, additions_subtractions=42,
                                exact_degree=148, witnesses=19, output_register='polynomial'),
                retained_positive_witnesses=RETAINED, comparisons=pairs,
                polynomial_schedule=polynomial, common_registers=84,
                unchanged_common_gates_after_coordinate_renaming=83,
                reconstructed_root='tau_old=X*Y^2*(eta+zeta)+tau_gap',
                full_parent_polynomial_identities=512, original19_polynomial_identities=512,
                assignment_counts=dict(counts))


def verify_degree():
    polynomial = sources()[3]
    t = sp.Symbol('t')
    records = []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        s = {name: 1+(index+shift) % 4 for index, name in enumerate(RETAINED+['x'])}
        inputs = {name: sp.Poly(s[name]*t+index+1, t) for index, name in enumerate(RETAINED+['x'])}
        inputs.update(B=B, DC=3, DR=5, MC=10, MF=12, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(inputs))
        factors = [sp.Poly(env[name], t) for name in prior.FACTOR_NAMES]
        assert tuple(factor.degree() for factor in factors) == FACTOR_DEGREES
        k = s['eta']+s['zeta']
        first_top = s['w']*s['s']**2*k*(B-1)**9*s['Jrep']**9*(2*s['tau_gap']-k)
        assert factors[0].LC() == first_top
        Ctop = (B-1)*s['Jrep']-s['F']-s['Z']-s['alpha']-2*d*s['x']
        top = (-32*(B-1)**96*s['h']*(s['rho']+s['sigma'])*s['delta']**2*s['i']**2
               *s['j']*s['f']**2*k**9*s['w']**12*s['s']**20*s['Jrep']**96
               *Ctop*(2*s['tau_gap']-k))
        actual = sp.Poly(env['polynomial'], t)
        assert actual.degree() == 148 and actual.LC() == top
        records.append(dict(B=B, cell_bits=d, scales=s, factor_degrees=FACTOR_DEGREES,
                            exact_degree=148, leading_coefficient=str(top)))
    return dict(fixtures=records,
                highest_homogeneous_term='-32*(B-1)^96*h*(rho+sigma)*delta^2*i^2*j*f^2*(eta+zeta)^9*w^12*s^20*Jrep^96*C_top*(2*tau_gap-eta-zeta)',
                C_top='(B-1)*Jrep-F-Z-alpha-2*cell_bits*x')


def verify_bijection():
    V, k, g = sp.symbols('V k g')
    assert sp.expand((V*k+g)**2-V*(V+1)*k*k-(g*g+V*k*(2*g-k))) == 0
    cases = 0
    for V in range(1, 33):
        P = 2*V+1
        root, half_k = 1, 0
        for _ in range(12):
            root, half_k = P*root+(P*P-1)*half_k, root+P*half_k
            k = 2*half_k
            g = root-V*k
            assert root*root-V*(V+1)*k*k == 1
            assert g > 0 and g*g+V*k*(2*g-k) == 1
            assert V*k+g == root
            cases += 1
    return dict(symbolic_norm_identity=True, positive_component_bijection_fixtures=cases,
                scope='Component Pell tuples supplement the positive parametric proof; these are not complete compiler witnesses')


def verify():
    return dict(status='PASS_COMPLETE75_POSITIVE_ROOT89', source=verify_source(),
                degree=verify_degree(), positive_bijection=verify_bijection(),
                established_complete_comparison_bound=75,
                limits='This is a positive witness coordinate change, not equality of polynomials at the same coordinates. '
                       'The two ratio slacks and the complete strong auxiliary and ordinary-input constraints remain present.')


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
