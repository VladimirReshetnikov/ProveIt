"""Retaining the strong comparison gives91/130 and93/90 from coupled88."""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_coupled_index_linear88 as prior
import complete75_norm_product91 as partitions

eliminated = prior.eliminated
RETAINED = prior.RETAINED
FACTORS = tuple(name for name in prior.FACTOR_NAMES if name != 'norm_strong')
DEGREES = (14, 22, 42, 28, 9, 5, 9)
VARIANTS = {
    '91_degree130': (((0, 2, 4), (1, 3, 5, 6)), 91, 130),
    '93_degree90': (((2,), (0, 3), (1, 4, 5, 6)), 93, 90),
}


def sources(name):
    partition, _, _ = VARIANTS[name]
    original, old, _, _ = prior.sources()
    nodes = {key: (op, left, right) for key, op, left, right in old}
    comparisons = [('ic22', 'R16')]
    for group_index, group in enumerate(partition):
        last = FACTORS[group[0]]
        for index, factor in enumerate(group[1:], 1):
            target = f'group_{group_index}_{index}'
            nodes[target] = ('*', last, FACTORS[factor])
            last = target
        comparisons.append((last, 1))
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    active, done, certificate = set(), set(available), []

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

    for left, right in comparisons:
        visit(left)
        visit(right)
    assert len(certificate) == 78+7-len(partition)
    names = {key for key, _, _, _ in certificate}
    assert 'strong_difference' not in names and 'norm_strong' not in names
    assert all(key in names for key in FACTORS)
    polynomial, output = eliminated.polynomial_schedule(certificate, comparisons)
    return original, certificate, comparisons, polynomial, output


def identity_checks(name, polynomial, output):
    original = sources(name)[0]
    partition = VARIANTS[name][0]
    rng, counts = random.Random(91130+len(partition)), Counter()
    for case in range(512):
        signed = case >= 384
        supplied = {key: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
                    for key in RETAINED+['x']}
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
        q = (B-1)*supplied['Jrep']+1
        X, Y = supplied['w']*q**3, supplied['s']*q**3
        k = supplied['eta']+supplied['zeta']
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'tau': X*Y*Y*k+supplied['tau_gap'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    'zquot': supplied['zplus']-1,
                    **{key: env[register] for key, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        old = eliminated.run(original, eliminated.fixed_inputs(full))
        r = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        U = supplied['j']*env['R10a']-env['r_lhs']
        V, T2, y2 = env['aux_u_rhs'], env['ic22'], supplied['y_aux']**2
        factors = (1-r[5], 1+r[11], 1+r[17],
                   1+r[13]-T2*r[14]*(U+V)-r[12]*(V*V-y2),
                   1+r[8], 1+r[2], 1+r[8]-r[14])
        assert [env[key] for key in FACTORS] == list(factors)
        expected = r[12]**2
        for group in partition:
            product = 1
            for i in group:
                product *= factors[i]
            expected += (product-1)**2
        assert env[output] == expected
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['zero_restored_quotient'] += restored['zquot'] == 0
    return dict(original19_full_polynomial_identities=512, counts=counts)


def degree_checks(name, polynomial, output):
    partition, _, degree = VARIANTS[name]
    t, records = sp.Symbol('t'), []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        s = {key: 1+(index+shift) % 4 for index, key in enumerate(RETAINED+['x'])}
        inputs = {key: sp.Poly(s[key]*t+index+1, t) for index, key in enumerate(RETAINED+['x'])}
        inputs.update(B=B, DC=3, DR=5, MC=B-2, MF=4, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(inputs))
        factors = [sp.Poly(env[key], t) for key in FACTORS]
        assert tuple(factor.degree() for factor in factors) == DEGREES
        Q, k = (B-1)*s['Jrep'], s['eta']+s['zeta']
        gamma = s['rho']+s['sigma']
        Ctop = Q-s['F']-s['Z']-s['alpha']-2*d*s['x']
        first_gap = 2*s['tau_gap']-k
        forms = (s['w']*s['s']**2*k*Q**9*first_gap,
                 8*gamma*k*s['w']**2*s['s']**3*Q**15,
                 -4*s['delta']**2*s['w']**5*s['s']**5*Q**30,
                 s['f']**2*k*k*s['w']**2*s['s']**4*Q**18,
                 -s['h']*s['w']*s['s']*Q**6,
                 s['w']*Q**3*Ctop,
                 -s['h']*s['w']*s['s']*Q**6)
        assert tuple(factor.LC() for factor in factors) == forms
        group_degrees = [sum(DEGREES[i] for i in group) for group in partition]
        top = 0
        for group, group_degree in zip(partition, group_degrees):
            if 2*group_degree == degree:
                value = 1
                for i in group:
                    value *= forms[i]
                top += value*value
        if degree == 130:
            explicit_top = 16*Q**90*s['h']**2*s['delta']**4*k*k*s['w']**14*s['s']**16*first_gap**2
        else:
            explicit_top = 64*Q**60*s['h']**4*gamma*gamma*k*k*s['w']**10*s['s']**10*Ctop*Ctop
        actual = sp.Poly(env[output], t)
        assert top == explicit_top and actual.degree() == degree and actual.LC() == top
        records.append(dict(B=B, cell_bits=d, scales=s, group_degrees=group_degrees,
                            exact_degree=degree, leading_coefficient=str(top)))
    return records


def verify_variant(name):
    partition, cost, degree = VARIANTS[name]
    _, certificate, comparisons, polynomial, output = sources(name)
    old_nodes = {key: (op, left, right) for key, op, left, right in prior.sources()[1]}
    for key, op, left, right in certificate:
        if key in old_nodes:
            assert old_nodes[key] == (op, left, right)
        else:
            assert key.startswith('group_') and op == '*'
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for key, op, left, right in polynomial:
        assert key not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(key)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    g = len(partition)
    assert len(polynomial) == cost == 87+2*g
    assert cc == {'M':47-g, 'A':38} and pc == {'M':48, 'A':39+2*g}
    assert len(comparisons) == g+1
    possible = [p for p in partitions.set_partitions(list(range(7))) if len(p) == g]
    best = min(max(sum(DEGREES[i] for i in group) for group in p) for p in possible)
    assert 2*best == degree
    return dict(partition=partition, factor_names=FACTORS, factor_degrees=DEGREES,
                positive_witnesses=RETAINED,
                certificate=dict(operations=len(certificate), multiplications=cc['M'],
                                 additions_subtractions=cc['A'], equations=g+1, witnesses=19),
                polynomial=dict(operations=cost, multiplications=pc['M'], additions_subtractions=pc['A'],
                                exact_degree=degree, witnesses=19, output_register=output),
                retained_strong_comparison=['ic22', 'R16'], comparisons=comparisons,
                polynomial_schedule=polynomial,
                source_identities=identity_checks(name, polynomial, output),
                degree_fixtures=degree_checks(name, polynomial, output),
                partition_audit=dict(candidates=len(possible), minimum_largest_group_degree=best,
                                     scope='Only partitions of these seven fixed factors with the retained strong comparison'))


def verify():
    return dict(status='PASS_COMPLETE75_COUPLED88_DEGREE_TRADEOFFS',
                variants={name: verify_variant(name) for name in VARIANTS},
                fixed_hypotheses='The complete compiler mask and positivity hypotheses of coupled_index_linear88',
                established_complete_comparison_bound=75,
                limits='The exact strong square is retained as a separate equation. '
                       'Multiplying the group equations restores the proved88 source, including its compiler-dependent sign proof.')


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
