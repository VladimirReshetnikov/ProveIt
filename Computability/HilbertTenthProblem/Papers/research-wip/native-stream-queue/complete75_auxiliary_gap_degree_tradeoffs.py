"""Positive auxiliary-gap coordinates: 90/131, 91/128, 98/54, 99/52."""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import random

import sympy as sp

import complete75_linear_input_degree_tradeoffs as parent

prior = parent.prior
eliminated = prior.eliminated
RETAINED = ['aux_gap' if name == 'y_aux' else name for name in prior.RETAINED]
COUPLED_FACTORS = parent.COUPLED_FACTORS
SIX_FACTORS = parent.SIX_FACTORS
VARIANTS = {
    '90_degree131': ('coupled_product', None, 90, 131),
    '91_degree128': ('uncoupled_product', None, 91, 128),
    '98_degree54': ('six', ((0, 4), (1, 5), (2,), (3,)), 98, 54),
    '99_degree52': ('coupled', ((0, 4), (1,), (2,), (3,), (5, 6)), 99, 52),
}


def sources(name, recoded=True):
    family, partition, _, _ = VARIANTS[name]
    original, old, _, _ = prior.sources()
    nodes = {key: (op, left, right) for key, op, left, right in old}
    if recoded:
        assert 'y_aux' not in nodes
        nodes['y_aux'] = ('+', 'aux_u_rhs', 'aux_gap')
    if family in ('uncoupled_product', 'six'):
        nodes['H17'] = ('-', 'jc', 'r_lhs')
    if family == 'uncoupled_product':
        nodes['linear_difference'] = ('-', 'aux_u_rhs', 'H17')
        nodes['norm_linear'] = ('+', 'linear_difference', 1)
    if family.endswith('_product'):
        comparisons = [('eight_units', 1)]
    else:
        comparisons = [('ic22', 'R16')]
        factors = COUPLED_FACTORS if family == 'coupled' else SIX_FACTORS
        if family == 'six':
            comparisons.append(('H17', 'aux_u_rhs'))
        for group_index, group in enumerate(partition):
            last = factors[group[0]]
            for index, factor in enumerate(group[1:], 1):
                key = f'group_{group_index}_{index}'
                nodes[key] = ('*', last, factors[factor])
                last = key
            comparisons.append((last, 1))
    witnesses = RETAINED if recoded else prior.RETAINED
    free = set(witnesses+eliminated.baseline.prior.CONSTANTS+['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    active, done, certificate = set(), set(free), []

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
    if family.endswith('_product'):
        polynomial = certificate+[('polynomial', '-', 'eight_units', 1)]
        output = 'polynomial'
    else:
        polynomial, output = eliminated.polynomial_schedule(certificate, comparisons)
    return original, certificate, comparisons, polynomial, output


def restored_values(values):
    q = (values['B']-1)*values['Jrep']+1
    c = (values['eta']+values['zeta'])*values['s']*q**3+values['eta']
    V = values['o']*values['f']-c
    return {**values, 'y_aux': V+values['aux_gap']}


def expected_polynomial(name, values):
    family, partition, _, _ = VARIANTS[name]
    f = prior.manual_factors(restored_values(values))
    if family == 'coupled_product':
        return parent.product(f)-1
    if family == 'uncoupled_product':
        return parent.product(f[:-1])*(f[-1]-f[4]+1)-1
    ordered = f[:6]+(f[-1],) if family == 'coupled' else f[:6]
    result = (f[6]-1)**2
    if family == 'six':
        result += (f[4]-f[-1])**2
    return result+sum((parent.product(ordered[i] for i in group)-1)**2 for group in partition)


def source_checks(name):
    family, partition, cost, degree = VARIANTS[name]
    _, certificate, comparisons, polynomial, output = sources(name)
    _, old, oldpairs, oldpoly, oldout = sources(name, recoded=False)
    old_nodes = {key: (op, left, right) for key, op, left, right in old}
    new_nodes = {key: (op, left, right) for key, op, left, right in certificate}
    assert new_nodes.keys()-old_nodes.keys() == {'y_aux'}
    assert {key: new_nodes[key] for key in old_nodes} == old_nodes
    assert new_nodes['y_aux'] == ('+', 'aux_u_rhs', 'aux_gap')
    assert comparisons == oldpairs and len(certificate) == len(old)+1
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for key, op, left, right in polynomial:
        assert key not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(key)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert len(polynomial) == cost
    assert pc == {'M': 47 if family.endswith('_product') else 48,
                  'A': cost-(47 if family.endswith('_product') else 48)}
    assert len(RETAINED) == len(set(RETAINED)) == 19 and 'y_aux' not in RETAINED
    rng, counts = random.Random(90000+cost), Counter()
    for case in range(512):
        signed = case >= 384
        values = {key: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
                  for key in RETAINED+['x']}
        values['F'] = rng.randrange(-200, 201) if signed else rng.randrange(1, 200)
        B = rng.choice((16, 32, 64, 256))
        values.update(B=B, DC=3, DR=5, MC=B-2, MF=4,
                      cell_bits=B.bit_length()-1, inner_bits=3)
        if case % 5 == 0:
            values['zplus'] = 1
        env = eliminated.run(polynomial, eliminated.fixed_inputs(values))
        if case < 4:
            values['F'] += 2*abs(env['exponent_rhs'])+1
            env = eliminated.run(polynomial, eliminated.fixed_inputs(values))
        restored = restored_values(values)
        oldenv = eliminated.run(oldpoly, eliminated.fixed_inputs(restored))
        assert env[output] == oldenv[oldout] == expected_polynomial(name, values)
        assert all(env[key] == oldenv[key] for key in old_nodes)
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['negative_computed_y'] += env['y_aux'] < 0
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['zero_restored_quotient'] += values['zplus'] == 1
    assert counts['negative_computed_mu'] >= 4 and counts['negative_computed_y'] > 0
    return dict(family=family, partition=partition,
                certificate=dict(operations=len(certificate), multiplications=cc['M'],
                                 additions_subtractions=cc['A'], equations=len(comparisons), witnesses=19),
                polynomial=dict(operations=cost, multiplications=pc['M'], additions_subtractions=pc['A'],
                                exact_degree=degree, witnesses=19, output_register=output),
                positive_witnesses=RETAINED, comparisons=comparisons, polynomial_schedule=polynomial,
                direct_polynomial_identities=512, coordinate_substitution_identities=512,
                assignment_counts=dict(counts))


def highest_forms(scales, B, d):
    f = list(parent.highest_forms(scales, B, d))
    Q, k = (B-1)*scales['Jrep'], scales['eta']+scales['zeta']
    f[3] = 2*scales['aux_gap']*scales['f']**2*k*scales['w']**2*scales['s']**3*Q**15
    return f


def degree_checks(name):
    family, partition, _, degree = VARIANTS[name]
    _, _, _, polynomial, output = sources(name)
    t, records = sp.Symbol('t'), []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        scales = {key: 1+(index+shift) % 4 for index, key in enumerate(RETAINED+['x'])}
        scales.update(delta=2+shift, rho=5+shift, tau_gap=7+shift)
        inputs = {key: sp.Poly(scales[key]*t+index+1, t) for index, key in enumerate(RETAINED+['x'])}
        inputs.update(B=B, DC=3, DR=5, MC=B-2, MF=4, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(inputs))
        forms = highest_forms(scales, B, d)
        if family.endswith('_product'):
            uncoupled = family == 'uncoupled_product'
            degrees = (14,22,26,24,9,5,22,6 if uncoupled else 9)
            selected = forms[:7]+[forms[8] if uncoupled else forms[7]]
            names = prior.FACTOR_NAMES
            top, group_degrees = parent.product(selected), None
        else:
            names = COUPLED_FACTORS if family == 'coupled' else SIX_FACTORS
            degrees = (14,22,26,24,9,5,9) if family == 'coupled' else (14,22,26,24,9,5)
            selected = forms[:6]+[forms[7]] if family == 'coupled' else forms[:6]
            group_degrees = [sum(degrees[i] for i in group) for group in partition]
            top = sum(parent.product(selected[i] for i in group)**2
                      for group, gd in zip(partition, group_degrees) if 2*gd == degree)
            assert sp.Poly(env['ic22']-env['R16'], t).degree() == 22
            if family == 'six':
                assert sp.Poly(env['H17']-env['aux_u_rhs'], t).degree() == 6
        factors = [sp.Poly(env[key], t) for key in names]
        assert tuple(f.degree() for f in factors) == degrees
        assert [f.LC() for f in factors] == selected
        actual = sp.Poly(env[output], t)
        assert actual.degree() == degree and actual.LC() == top
        records.append(dict(B=B, cell_bits=d, scales=scales, factor_degrees=degrees,
                            group_degrees=group_degrees, exact_degree=degree, leading_coefficient=str(top)))
    return records


def gap_checks():
    K, V, e = sp.symbols('K V e')
    expanded = K*(V*V-(V+e)**2)+(V+e)**2
    assert sp.expand(expanded-(V*V-(K-1)*e*(2*V+e))) == 0
    count = 0
    for T in range(2, 25):
        for odd in range(3, 26, 2):
            root, y = prior.prior.pell(T, odd)
            assert root % T == 0
            V = root//T
            e = y-V
            assert V > 1 and e > 0 and y == V+e
            assert T*T*(V*V-y*y)+y*y == 1
            assert (T*T-1)*(y*y-V*V) == V*V-1
            count += 1
    residues = 0
    for A in range(4):
        for f in range(4):
            K = (A*A-1)*(f*f-1)
            assert K % 4 in (0, 1)
            for V in range(4):
                for e in range(4):
                    y = V+e
                    assert (K*(V*V-y*y)+y*y) % 4 != 3
                    residues += 1
    return dict(symbolic_gap_identity=True, positive_auxiliary_Pell_maps=count,
                modulo_four_cases=residues,
                scope='Local auxiliary norms and arbitrary-integer identities; no complete compiler zeros claimed.')


def partition_audit():
    families = {
        'coupled_strong_separate': ((14,22,26,24,9,5,9),89,22,[109,55,38,31,26,26,26]),
        'coupled_eight_units': ((14,22,26,24,9,5,22,9),89,0,[131,66,44,36,31,26,26,26]),
        'uncoupled_strong_separate': ((14,22,26,24,9,5,6),90,22,[106,53,36,28,26,26,26]),
        'five_units_three_comparisons': ((14,22,26,24,9),91,22,[95,48,36,26,26]),
        'six_units_two_comparisons': ((14,22,26,24,9,5),90,22,[100,50,36,27,26,26]),
    }
    result = {}
    for name, (weights, base, outside, expected) in families.items():
        best, counts = {}, defaultdict(int)
        for partition in parent.set_partitions(len(weights)):
            g = len(partition)
            counts[g] += 1
            largest = max([outside]+[sum(weights[i] for i in group) for group in partition])
            if g not in best or largest < best[g][0]:
                best[g] = largest, partition
        assert [best[g][0] for g in range(1,len(weights)+1)] == expected
        result[name] = dict(weights=weights,
                            scope='Only fixed-factor partitions with the stated literal SOS schedule.',
                            choices=[dict(groups=g, partitions=counts[g], operations=base+2*g,
                                          degree=2*best[g][0], example=best[g][1])
                                     for g in range(1,len(weights)+1)])
    return result


def verify():
    return dict(variants={name: dict(source=source_checks(name), degree=degree_checks(name)) for name in VARIANTS},
                gap_checks=gap_checks(), partition_audit=partition_audit())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(path.read_text()) == json.loads(json.dumps(result))
    print('auxiliary-gap degree tradeoffs: 90/131,91/128,98/54,99/52; PASS')
