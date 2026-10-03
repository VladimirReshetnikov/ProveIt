"""Linear input modulus tradeoffs: 90/132,92/114,94/80,95/72,96/62,97/56."""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import random

import sympy as sp

import complete75_linear_input_modulus89 as prior

eliminated = prior.eliminated
RETAINED = prior.RETAINED
COUPLED_FACTORS = tuple(name for name in prior.FACTOR_NAMES if name != 'norm_strong')
SIX_FACTORS = COUPLED_FACTORS[:-1]
COUPLED_DEGREES = (14, 22, 26, 28, 9, 5, 9)
VARIANTS = {
    '90_degree132': ('uncoupled', None, 90, 132),
    '92_degree114': ('coupled', ((0, 3, 4, 5), (1, 2, 6)), 92, 114),
    '94_degree80': ('coupled', ((0, 1), (2, 4, 5), (3, 6)), 94, 80),
    '95_degree72': ('six', ((0, 1), (2, 4), (3, 5)), 95, 72),
    '96_degree62': ('coupled', ((0, 4, 5), (1, 6), (2,), (3,)), 96, 62),
    '97_degree56': ('six', ((0, 4, 5), (1,), (2,), (3,)), 97, 56),
}


def sources(name, smaller_modulus=True):
    family, partition, _, _ = VARIANTS[name]
    original, old, _, _ = prior.sources()
    nodes = {key: (op, left, right) for key, op, left, right in old}
    if not smaller_modulus:
        assert nodes.pop('a_plus_one') == ('+', 'R12', 1)
        nodes['index_product'] = ('*', 'delta', 'A')
    if family in ('uncoupled', 'six'):
        nodes['H17'] = ('-', 'jc', 'r_lhs')
    if family == 'uncoupled':
        nodes['linear_difference'] = ('-', 'aux_u_rhs', 'H17')
        nodes['norm_linear'] = ('+', 'linear_difference', 1)
        comparisons = [('eight_units', 1)]
    else:
        comparisons = [('ic22', 'R16')]
        factors = COUPLED_FACTORS if family == 'coupled' else SIX_FACTORS
        if family == 'six':
            comparisons.append(('H17', 'aux_u_rhs'))
        for group_index, group in enumerate(partition):
            last = factors[group[0]]
            for index, factor in enumerate(group[1:], 1):
                target = f'group_{group_index}_{index}'
                nodes[target] = ('*', last, factors[factor])
                last = target
            comparisons.append((last, 1))
    free = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
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
    if family == 'uncoupled':
        polynomial = certificate+[('polynomial', '-', 'eight_units', 1)]
        output = 'polynomial'
    else:
        polynomial, output = eliminated.polynomial_schedule(certificate, comparisons)
    return original, certificate, comparisons, polynomial, output


def product(values):
    result = 1
    for value in values:
        result *= value
    return result


def expected_polynomial(name, values):
    family, partition, _, _ = VARIANTS[name]
    factors = prior.manual_factors(values)
    if family == 'uncoupled':
        return product(factors[:-1])*(factors[-1]-factors[4]+1)-1
    ordered = factors[:6]+(factors[-1],) if family == 'coupled' else factors[:6]
    result = (factors[6]-1)**2
    if family == 'six':
        result += (factors[4]-factors[-1])**2
    return result+sum((product(ordered[i] for i in group)-1)**2 for group in partition)


def source_checks(name):
    family, partition, cost, degree = VARIANTS[name]
    _, certificate, comparisons, polynomial, output = sources(name)
    _, old, oldpairs, oldpoly, oldout = sources(name, smaller_modulus=False)
    old_nodes = {key: (op, left, right) for key, op, left, right in old}
    new_nodes = {key: (op, left, right) for key, op, left, right in certificate}
    assert new_nodes.keys()-old_nodes.keys() == {'a_plus_one'}
    assert not old_nodes.keys()-new_nodes.keys()
    assert {key for key in old_nodes if old_nodes[key] != new_nodes[key]} == {'index_product'}
    assert comparisons == oldpairs
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for key, op, left, right in polynomial:
        assert key not in available and op in ('+', '-', '*')
        assert all(isinstance(value, int) or value in available for value in (left, right))
        available.add(key)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert len(polynomial) == cost and pc == {'M': 47 if family == 'uncoupled' else 48,
                                             'A': cost-(47 if family == 'uncoupled' else 48)}
    if family == 'uncoupled':
        assert len(certificate) == 89 and len(comparisons) == 1
    else:
        g = len(partition)
        assert len(certificate) == (86-g if family == 'coupled' else 84-g)
        assert len(comparisons) == g+(1 if family == 'coupled' else 2)
        assert 'strong_difference' not in new_nodes and 'norm_strong' not in new_nodes
        if family == 'six':
            assert 'norm_linear' not in new_nodes and 'linear_difference' not in new_nodes
    rng, counts = random.Random(1000+cost), Counter()
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
        assert env[output] == expected_polynomial(name, values)
        oldenv = eliminated.run(oldpoly, eliminated.fixed_inputs(values))
        forward = {**values, 'delta': values['delta']*(oldenv['R12']+3)}
        newenv = eliminated.run(polynomial, eliminated.fixed_inputs(forward))
        assert newenv[output] == oldenv[oldout]
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['zero_restored_quotient'] += values['zplus'] == 1
    return dict(family=family, partition=partition,
                certificate=dict(operations=len(certificate), multiplications=cc['M'],
                                 additions_subtractions=cc['A'], equations=len(comparisons), witnesses=19),
                polynomial=dict(operations=cost, multiplications=pc['M'], additions_subtractions=pc['A'],
                                exact_degree=degree, witnesses=19, output_register=output),
                positive_witnesses=RETAINED, comparisons=comparisons, polynomial_schedule=polynomial,
                direct_polynomial_identities=512, forward_coordinate_polynomial_identities=512,
                assignment_counts=dict(counts))


def highest_forms(s, B, d):
    Q = (B-1)*s['Jrep']
    k, gamma = s['eta']+s['zeta'], s['rho']+s['sigma']
    w, y = s['w'], s['s']
    Ctop = Q-s['F']-s['Z']-s['alpha']-2*d*s['x']
    return (w*y*y*k*Q**9*(2*s['tau_gap']-k),
            8*gamma*k*w*w*y**3*Q**15,
            4*s['delta']*(2*s['rho']-s['delta'])*w**3*y**3*Q**18,
            s['f']**2*k*k*w*w*y**4*Q**18,
            -s['h']*w*y*Q**6, w*Q**3*Ctop,
            s['i']**2*k**4*y**4*Q**12, -s['h']*w*y*Q**6,
            -s['j']*k*y*Q**3)


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
        if family == 'uncoupled':
            degrees = (14, 22, 26, 28, 9, 5, 22, 6)
            actual_factors = [sp.Poly(env[key], t) for key in prior.FACTOR_NAMES]
            assert tuple(f.degree() for f in actual_factors) == degrees
            assert tuple(f.LC() for f in actual_factors) == forms[:7]+(forms[8],)
            top = product(forms[:7])*forms[8]
            group_degrees = None
        else:
            factors = COUPLED_FACTORS if family == 'coupled' else SIX_FACTORS
            degrees = COUPLED_DEGREES if family == 'coupled' else COUPLED_DEGREES[:-1]
            selected_forms = forms[:6]+(forms[7],) if family == 'coupled' else forms[:6]
            actual_factors = [sp.Poly(env[key], t) for key in factors]
            assert tuple(f.degree() for f in actual_factors) == degrees
            assert tuple(f.LC() for f in actual_factors) == selected_forms
            group_degrees = [sum(degrees[i] for i in group) for group in partition]
            top = sum(product(selected_forms[i] for i in group)**2
                      for group, group_degree in zip(partition, group_degrees) if 2*group_degree == degree)
            assert sp.Poly(env['ic22']-env['R16'], t).degree() == 22
            if family == 'six':
                assert sp.Poly(env['H17']-env['aux_u_rhs'], t).degree() == 6
        actual = sp.Poly(env[output], t)
        assert actual.degree() == degree and actual.LC() == top
        records.append(dict(B=B, cell_bits=d, scales=scales, factor_degrees=degrees,
                            group_degrees=group_degrees, exact_degree=degree, leading_coefficient=str(top)))
    return records


def set_partitions(n):
    groups = []
    def visit(index):
        if index == n:
            yield tuple(tuple(group) for group in groups)
            return
        for group in groups:
            group.append(index)
            yield from visit(index+1)
            group.pop()
        groups.append([index])
        yield from visit(index+1)
        groups.pop()
    yield from visit(0)


def partition_audit():
    families = {
        'coupled_strong_separate': ((14,22,26,28,9,5,9),88,22),
        'coupled_eight_units': ((14,22,26,28,9,5,22,9),88,0),
        'uncoupled_strong_separate': ((14,22,26,28,9,5,6),89,22),
        'five_units_three_comparisons': ((14,22,26,28,9),90,22),
        'six_units_two_comparisons': ((14,22,26,28,9,5),89,22),
    }
    expected_minima = {
        'coupled_strong_separate': [113,57,40,31,28,28,28],
        'coupled_eight_units': [135,68,46,36,31,28,28,28],
        'uncoupled_strong_separate': [110,55,37,28,28,28,28],
        'five_units_three_comparisons': [99,50,36,28,28],
        'six_units_two_comparisons': [104,53,36,28,28,28],
    }
    result = {}
    for name, (weights, base, outside_degree) in families.items():
        best, counts = {}, defaultdict(int)
        for partition in set_partitions(len(weights)):
            g = len(partition)
            counts[g] += 1
            largest = max([outside_degree]+[sum(weights[i] for i in group) for group in partition])
            if g not in best or largest < best[g][0]:
                best[g] = largest, partition
        assert [best[g][0] for g in range(1,len(weights)+1)] == expected_minima[name]
        result[name] = dict(weights=weights, scope='Minimum degree among set partitions of these fixed factors in the stated literal SOS family.',
                            choices=[dict(groups=g, partitions=counts[g], operations=base+2*g,
                                          degree=2*best[g][0], example=best[g][1])
                                     for g in range(1,len(weights)+1)])
    return result


def verify():
    return dict(variants={name: dict(source=source_checks(name), degree=degree_checks(name)) for name in VARIANTS},
                partition_audit=partition_audit())


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
    print('linear input degree tradeoffs: 90/132,92/114,94/80,95/72,96/62,97/56; PASS')
