"""Retained auxiliary comparisons give universal polynomial tradeoffs 93/128,92/136.

The rewritten auxiliary factor agrees with the old norm on the two unchanged
auxiliary equations. This does not assert equality off their joint zero set.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_norm_product91 as five
import complete75_norm_product90 as six


eliminated = five.eliminated
VARIANTS = {
    '93_degree128': (five, ((1, 2), (0, 3, 4)), (26, 22, 42, 28, 9), 93, 128),
    '92_degree136': (six, ((0, 2), (1, 3, 4, 5)), (26, 22, 42, 28, 9, 5), 92, 136),
}


def sources(name):
    prior, partition, _, _, _ = VARIANTS[name]
    original, old, pairs = prior.partition_sources(partition)
    nodes = {register: (op, left, right) for register, op, left, right in old}
    assert nodes['H2'] == ('*', 'H17', 'H17')
    assert nodes['L17'] == ('*', 'ic22', 'aux_square_gap')
    nodes['H2'] = ('*', 'aux_u_rhs', 'aux_u_rhs')
    nodes['L17'] = ('*', 'R16', 'aux_square_gap')
    free = set(prior.RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
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
    forms = [-k*k*w*w*s**4*Q**18,
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
    rng = random.Random(93128 if prior is five else 92136)
    counts = Counter()
    for case in range(256):
        supplied = {key: rng.randrange(1, 10) for key in prior.RETAINED+['x']}
        supplied['F'] = rng.randrange(1, 200)
        if prior is six and case % 5 == 0:
            supplied['zplus'] = 1
        constants = dict(B=rng.choice((16, 32, 64, 256)), DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        if case < 4:
            supplied['F'] += 2*abs(env['exponent_rhs'])+1
            env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
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
        scales = {key: 1+(index+shift) % 4 for index, key in enumerate(prior.RETAINED+['x'])}
        inputs = {key: sp.Poly(scales[key]*t+index+1, t)
                  for index, key in enumerate(prior.RETAINED+['x'])}
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
        actual = sp.Poly(env[output], t)
        assert actual.degree() == degree and actual.LC() == top
        result.append(dict(B=B, cell_bits=d, scales=scales, group_degrees=group_degrees,
                           exact_degree=degree, leading_coefficient=str(top)))
    return result


def verify_variant(name):
    prior, partition, degrees, cost, degree = VARIANTS[name]
    _, certificate, pairs, polynomial, output = sources(name)
    _, old, oldpairs = prior.partition_sources(partition)
    changed = {register for register, op, left, right in certificate
               if (op, left, right) != {n: (o, l, r) for n, o, l, r in old}[register]}
    assert changed == {'H2', 'L17'} and pairs == oldpairs
    available = set(prior.RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for register, op, left, right in polynomial:
        assert register not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(register)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert len(polynomial) == cost and pc == {'M':49, 'A':cost-49}
    assert cc == ({'M':44, 'A':35} if prior is five else {'M':45, 'A':36})
    assert len(pairs) == (5 if prior is five else 4)
    partitions = [p for p in five.set_partitions(list(range(len(degrees)))) if len(p) == 2]
    best = min(max(sum(degrees[i] for i in group) for group in p) for p in partitions)
    assert 2*best == degree
    return dict(partition=partition, factor_degrees=degrees, positive_witnesses=prior.RETAINED,
                certificate=dict(operations=len(certificate), multiplications=cc['M'],
                                 additions_subtractions=cc['A'], equations=len(pairs), witnesses=19),
                polynomial=dict(operations=cost, multiplications=pc['M'], additions_subtractions=pc['A'],
                                exact_degree=degree, witnesses=19, output_register=output),
                preserved_source_gates=len(certificate)-2, changed_registers=sorted(changed),
                comparisons=pairs, polynomial_schedule=polynomial,
                source_identities=identity_checks(name, polynomial, output),
                degree_fixtures=degree_checks(name, polynomial, output),
                two_group_partition_audit=dict(candidates=len(partitions), minimum_largest_degree=best,
                                                scope='Only partitions of these fixed factors and literal circuits'))


def verify():
    K, T2, U, V, y = sp.symbols('K T2 U V y')
    old, new = T2*(U*U-y*y)+y*y, K*(V*V-y*y)+y*y
    assert sp.expand(new-old+(T2-K)*(V*V-y*y)+T2*(U-V)*(U+V)) == 0
    return dict(status='PASS_COMPLETE75_AUXILIARY_DEGREE_TRADEOFFS',
                variants={name: verify_variant(name) for name in VARIANTS},
                exact_auxiliary_correction_identity=True,
                established_complete_comparison_bound=75,
                limits='Both strong and linear auxiliary comparisons are retained. '
                       'Conditional source equivalence preserves positive integer zeros; '
                       'the new and old auxiliary factors differ away from those comparisons.')


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
