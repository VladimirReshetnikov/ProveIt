"""Positive first-root coordinates give universal tradeoffs94/84,93/118 and92/122.

The full strong and linear auxiliary comparisons remain. Positive witness
sets are in bijection through tau_old=X*Y^2*(eta+zeta)+tau_gap.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_norm_product91 as five
import complete75_norm_product90 as six
import complete75_positive_root89 as root_coordinate


eliminated = five.eliminated
VARIANTS = {
    '94_degree84': (six, ((0, 1), (2,), (3, 4, 5)), (14, 22, 42, 28, 9, 5), 94, 84),
    '93_degree118': (five, ((0, 2), (1, 3, 4)), (14, 22, 42, 28, 9), 93, 118),
    '92_degree122': (six, ((0, 2, 5), (1, 3, 4)), (14, 22, 42, 28, 9, 5), 92, 122),
}


def retained(prior):
    return ['tau_gap' if key == 'tau' else key for key in prior.RETAINED]


def sources(name, recoded=True):
    prior, partition, _, _, _ = VARIANTS[name]
    original, old, pairs = prior.partition_sources(partition)
    nodes = {register: (op, left, right) for register, op, left, right in old}
    assert nodes['H2'] == ('*', 'H17', 'H17')
    assert nodes['L17'] == ('*', 'ic22', 'aux_square_gap')
    nodes['H2'] = ('*', 'aux_u_rhs', 'aux_u_rhs')
    nodes['L17'] = ('*', 'R16', 'aux_square_gap')
    if recoded:
        nodes = {key: (op, 'tau_gap' if left == 'tau' else left,
                       'tau_gap' if right == 'tau' else right)
                 for key, (op, left, right) in nodes.items()}
        removed = {key: nodes.pop(key) for key in
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
    witnesses = retained(prior) if recoded else prior.RETAINED
    free = set(witnesses+eliminated.baseline.prior.CONSTANTS+['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    certificate, active, done = [], set(), set(free)

    def visit(register):
        if isinstance(register, int) or register in done:
            return
        assert register not in active
        active.add(register)
        op, left, right = nodes[register]
        visit(left)
        visit(right)
        certificate.append((register, op, left, right))
        active.remove(register)
        done.add(register)

    for left, right in pairs:
        visit(left)
        visit(right)
    assert len(certificate) == len(old) == len(nodes)
    assert ('ic22', 'R16') in pairs and ('H17', 'aux_u_rhs') in pairs
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    return original, certificate, pairs, polynomial, output


def highest_forms(v, B, d, shifted):
    Q = (B-1)*v['Jrep']
    k, gamma = v['eta']+v['zeta'], v['rho']+v['sigma']
    w, s = v['w'], v['s']
    forms = [w*s*s*k*Q**9*(2*v['tau_gap']-k),
             8*gamma*k*w*w*s**3*Q**15,
             -4*v['delta']**2*w**5*s**5*Q**30,
             v['f']**2*k*k*w*w*s**4*Q**18,
             -v['h']*w*s*Q**6]
    if shifted:
        forms.append(w*Q**3*(Q-v['F']-v['Z']-v['alpha']-2*d*v['x']))
    return forms


def identity_checks(name, polynomial, output):
    prior, partition, _, _, _ = VARIANTS[name]
    original = sources(name)[0]
    old_polynomial, old_output = sources(name, recoded=False)[3:]
    rng = random.Random(93118 if prior is five else 92122)
    counts = Counter()
    for case in range(512):
        signed = case >= 384
        supplied = {key: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
                    for key in retained(prior)+['x']}
        supplied['F'] = rng.randrange(-200, 201) if signed else rng.randrange(1, 200)
        if prior is six and case % 5 == 0:
            supplied['zplus'] = 1
        constants = dict(B=rng.choice((16, 32, 64, 256)), DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        if case < 4:
            supplied['F'] += 2*abs(env['exponent_rhs'])+1
            env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        q = (constants['B']-1)*supplied['Jrep']+1
        X, Y = supplied['w']*q**3, supplied['s']*q**3
        k = supplied['eta']+supplied['zeta']
        root = X*Y*Y*k+supplied['tau_gap']
        parent = eliminated.run(old_polynomial,
                                eliminated.fixed_inputs({**supplied, **constants, 'tau': root}))
        assert env[output] == parent[old_output]
        if not signed:
            assert root > 0 and env['first_root_base'] > 0
        restored = {'tau': root, 'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    **{key: env[register] for key, register in eliminated.DEFINITIONS.items()}}
        if prior is six:
            restored['zquot'] = supplied['zplus']-1
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        old = eliminated.run(original, eliminated.fixed_inputs(full))
        r = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        U, V, T2, y2 = env['H17'], env['aux_u_rhs'], env['ic22'], supplied['y_aux']**2
        corrected_aux = 1+r[13]-r[12]*(V*V-y2)-T2*r[14]*(U+V)
        factors = [1-r[5], 1+r[11], 1+r[17], corrected_aux, 1+r[8]]
        if prior is six:
            factors.append(1+r[2])
        actual_names = six.FACTOR_NAMES if prior is six else five.NORM_NAMES
        assert [env[register] for register in actual_names] == factors
        expected = r[12]**2+r[14]**2+(r[2]**2 if prior is five else 0)
        for group in partition:
            product = 1
            for index in group:
                product *= factors[index]
            expected += (product-1)**2
        assert env[output] == expected
        assert all(r[index] == 0 for index in five.bounded.DELETED_EQUALITIES)
        counts['original19_polynomial_identities'] += 1
        counts['parent_polynomial_identities'] += 1
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['negative_computed_C'] += env['marked_rhs'] < 0
        counts['negative_computed_R'] += env['r_lhs'] < 0
    assert counts['negative_computed_mu'] >= 4
    return dict(counts)


def degree_checks(name, polynomial, output):
    prior, partition, degrees, _, degree = VARIANTS[name]
    t = sp.Symbol('t')
    result = []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        scales = {key: 1+(index+shift) % 4 for index, key in enumerate(retained(prior)+['x'])}
        inputs = {key: sp.Poly(scales[key]*t+index+1, t)
                  for index, key in enumerate(retained(prior)+['x'])}
        inputs.update(B=B, DC=3, DR=5, MC=10, MF=12, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(inputs))
        names = six.FACTOR_NAMES if prior is six else five.NORM_NAMES
        factors = [sp.Poly(env[register], t) for register in names]
        forms = highest_forms(scales, B, d, prior is six)
        assert [factor.degree() for factor in factors] == list(degrees)
        assert [factor.LC() for factor in factors] == forms
        group_degrees = [sum(degrees[index] for index in group) for group in partition]
        top = 0
        for group, group_degree in zip(partition, group_degrees):
            if 2*group_degree == degree:
                coefficient = 1
                for index in group:
                    coefficient *= forms[index]
                top += coefficient**2
        Q = (B-1)*scales['Jrep']
        k = scales['eta']+scales['zeta']
        gamma = scales['rho']+scales['sigma']
        if prior is five:
            explicit_top = 64*Q**78*scales['h']**2*gamma**2*scales['f']**4*k**6*scales['w']**10*scales['s']**16
        else:
            Ctop = Q-scales['F']-scales['Z']-scales['alpha']-2*d*scales['x']
            if degree == 84:
                explicit_top = (16*scales['delta']**4*scales['w']**10*scales['s']**10*Q**60
                                +scales['h']**2*scales['f']**4*k**4*scales['w']**8*scales['s']**10*Q**54*Ctop*Ctop)
            else:
                explicit_top = (16*Q**84*scales['delta']**4*k*k*scales['w']**14*scales['s']**14
                                *Ctop*Ctop*(2*scales['tau_gap']-k)**2)
        actual = sp.Poly(env[output], t)
        assert top == explicit_top
        assert actual.degree() == degree and actual.LC() == top
        result.append(dict(B=B, cell_bits=d, scales=scales, group_degrees=group_degrees,
                           exact_degree=degree, leading_coefficient=str(top)))
    return result


def verify_variant(name):
    prior, partition, degrees, cost, degree = VARIANTS[name]
    _, certificate, pairs, polynomial, output = sources(name)
    _, old, oldpairs = prior.partition_sources(partition)
    old_nodes = {key: (op, 'tau_gap' if left == 'tau' else left,
                       'tau_gap' if right == 'tau' else right)
                 for key, op, left, right in old}
    new_nodes = {key: (op, left, right) for key, op, left, right in certificate}
    common = old_nodes.keys() & new_nodes.keys()
    changed = {key for key in common if old_nodes[key] != new_nodes[key]}
    assert changed == {'H2', 'L17', 'norm_first'} and pairs == oldpairs
    assert old_nodes.keys()-new_nodes.keys() == {'UM2', 'scaled_norm_coefficient', 'ratio_product2', 'L9'}
    assert new_nodes.keys()-old_nodes.keys() == {'first_root_base', 'twice_tau_gap', 'first_signed_gap', 'first_cross'}
    available = set(retained(prior)+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for register, op, left, right in polynomial:
        assert register not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(register)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert len(polynomial) == cost and pc == {'M':48, 'A':cost-48}
    assert cc == {'M':40+len(degrees)-len(partition), 'A':36 if prior is five else 37}
    assert len(pairs) == len(partition)+(3 if prior is five else 2)
    partitions = [p for p in five.set_partitions(list(range(len(degrees)))) if len(p) == len(partition)]
    best = min(max(sum(degrees[i] for i in group) for group in p) for p in partitions)
    assert 2*best == degree
    return dict(partition=partition, factor_degrees=degrees, positive_witnesses=retained(prior),
                certificate=dict(operations=len(certificate), multiplications=cc['M'],
                                 additions_subtractions=cc['A'], equations=len(pairs), witnesses=19),
                polynomial=dict(operations=cost, multiplications=pc['M'], additions_subtractions=pc['A'],
                                exact_degree=degree, witnesses=19, output_register=output),
                unchanged_common_gates_after_coordinate_renaming=len(common)-len(changed),
                changed_common_registers=sorted(changed), removed_registers=sorted(old_nodes.keys()-new_nodes.keys()),
                added_registers=sorted(new_nodes.keys()-old_nodes.keys()),
                comparisons=pairs, polynomial_schedule=polynomial,
                source_identities=identity_checks(name, polynomial, output),
                degree_fixtures=degree_checks(name, polynomial, output),
                group_partition_audit=dict(groups=len(partition), candidates=len(partitions), minimum_largest_degree=best,
                                                scope='Only partitions of these fixed factors and literal circuits'))


def verify():
    K, T2, U, V, y = sp.symbols('K T2 U V y')
    old, new = T2*(U*U-y*y)+y*y, K*(V*V-y*y)+y*y
    assert sp.expand(new-old+(T2-K)*(V*V-y*y)+T2*(U-V)*(U+V)) == 0
    return dict(status='PASS_COMPLETE75_POSITIVE_ROOT_DEGREE_TRADEOFFS',
                variants={name: verify_variant(name) for name in VARIANTS},
                exact_auxiliary_correction_identity=True,
                positive_root_bijection=root_coordinate.verify_bijection(),
                established_complete_comparison_bound=75,
                limits='Both strong and linear auxiliary comparisons are retained. '
                       'The root coordinate is changed by a proved positive bijection. '
                       'Auxiliary factors agree only on the two retained comparisons; no strong square is removed.')


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
    print(result['status'])
    for name, variant in result['variants'].items():
        print(name, variant['certificate'], variant['polynomial'])
