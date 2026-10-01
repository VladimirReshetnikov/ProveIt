"""A smaller input-index modulus gives 89=47M+42A, degree 135.

The positive witness change is delta_new=(a+3)*delta_old.  Positive
zero-set equivalence uses the complete coupled88 compiler hypotheses.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_coupled_index_linear88 as prior

eliminated = prior.eliminated
RETAINED = prior.RETAINED
FACTOR_NAMES = prior.FACTOR_NAMES
FACTOR_DEGREES = (14, 22, 26, 28, 9, 5, 22, 9)


def sources():
    original, old, pairs, _ = prior.sources()
    certificate = []
    for gate in old:
        name, op, left, right = gate
        if name == 'index_product':
            assert gate == ('index_product', '*', 'delta', 'A')
            certificate.append(('a_plus_one', '+', 'R12', 1))
            gate = (name, op, left, 'a_plus_one')
        certificate.append(gate)
    polynomial = certificate+[('polynomial', '-', 'eight_units', 1)]
    return original, certificate, pairs, polynomial


def manual_factors(values):
    B, J = values['B'], values['Jrep']
    q = (B-1)*J+1
    X, Y = values['w']*q**3, values['s']*q**3
    E = X*Y
    k = values['eta']+values['zeta']
    c = k*Y+values['eta']
    a, g = E+Y, values['tau_gap']
    H, Delta = 4*a+3, (a+2)**2-1
    D = X+a*c+(values['rho']+values['sigma'])*H
    input_index = 2*values['cell_bits']*values['x']+values['inner_bits']
    C = q-values['F']-values['Z']-values['alpha']-2*values['cell_bits']*values['x']
    W = C-values['Z']
    kappa = input_index+values['delta']*(a+1)
    mu = W+a*kappa+values['rho']*H
    K = Delta*(values['f']**2-1)
    V = values['o']*values['f']-c
    R = ((q*q-values['Z']-q*values['F'])*(q*q-1)
         +(values['MC']+q*(values['MF']+B-1))*J)
    index_base = k-values['h']*E
    return (g*g+E*k*Y*(2*g-k), D*D-Delta*c*c,
            mu*mu-Delta*kappa*kappa,
            K*(V*V-values['y_aux']**2)+values['y_aux']**2,
            index_base-R,
            (values['DC']+B*values['DR']+X)*C+q-values['F']-values['zplus']*(q-1),
            1+(values['i']*c*c)**2-K,
            V-values['j']*c+index_base)


def verify_source():
    _, certificate, pairs, polynomial = sources()
    _, old_certificate, old_pairs, old_polynomial = prior.sources()
    assert pairs == old_pairs == [('eight_units', 1)]
    old_nodes = {name: (op, left, right) for name, op, left, right in old_certificate}
    new_nodes = {name: (op, left, right) for name, op, left, right in certificate}
    assert new_nodes.keys()-old_nodes.keys() == {'a_plus_one'}
    assert not old_nodes.keys()-new_nodes.keys()
    assert {name for name in old_nodes if old_nodes[name] != new_nodes[name]} == {'index_product'}
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, op, left, right in polynomial:
        assert name not in available and op in ('+', '-', '*')
        assert all(isinstance(value, int) or value in available for value in (left, right))
        available.add(name)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert cc == {'M': 47, 'A': 41} and pc == {'M': 47, 'A': 42}
    rng, counts = random.Random(89135), Counter()
    for case in range(512):
        signed = case >= 384
        values = {name: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
                  for name in RETAINED+['x']}
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
        factors = manual_factors(values)
        assert tuple(env[name] for name in FACTOR_NAMES) == factors
        product = 1
        for factor in factors:
            product *= factor
        assert env['polynomial'] == product-1
        # This is a polynomial identity under the forward coordinate map,
        # independently of positivity or any source equality.
        old = eliminated.run(old_polynomial, eliminated.fixed_inputs(values))
        changed = {**values, 'delta': values['delta']*(old['R12']+3)}
        new = eliminated.run(polynomial, eliminated.fixed_inputs(changed))
        assert old['A'] == (old['R12']+1)*(old['R12']+3)
        assert all(new[name] == old[name] for name in FACTOR_NAMES)
        assert new['polynomial'] == old['polynomial']
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['zero_restored_quotient'] += values['zplus'] == 1
    return dict(certificate=dict(operations=88, multiplications=47, additions_subtractions=41,
                                 equations=1, witnesses=19),
                polynomial=dict(operations=89, multiplications=47, additions_subtractions=42,
                                exact_degree=135, witnesses=19, output_register='polynomial'),
                retained_positive_witnesses=RETAINED, comparisons=pairs,
                polynomial_schedule=polynomial,
                added_register='a_plus_one', changed_register='index_product',
                unchanged_parent_gates=86, direct_formula_identities=512,
                forward_coordinate_polynomial_identities=512, assignment_counts=dict(counts))


def verify_degree():
    polynomial = sources()[3]
    t, records = sp.Symbol('t'), []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        scales = {name: 1+(index+shift) % 4 for index, name in enumerate(RETAINED+['x'])}
        # Keep all displayed highest forms nonzero in each specialization.
        scales['delta'], scales['rho'], scales['tau_gap'] = 2+shift, 5+shift, 7+shift
        inputs = {name: sp.Poly(scales[name]*t+index+1, t)
                  for index, name in enumerate(RETAINED+['x'])}
        inputs.update(B=B, DC=3, DR=5, MC=B-2, MF=4, cell_bits=d, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(inputs))
        factors = [sp.Poly(env[name], t) for name in FACTOR_NAMES]
        assert tuple(factor.degree() for factor in factors) == FACTOR_DEGREES
        s = scales
        k, Q = s['eta']+s['zeta'], (B-1)*s['Jrep']
        Ctop = Q-s['F']-s['Z']-s['alpha']-2*d*s['x']
        input_top = 4*s['delta']*(2*s['rho']-s['delta'])*s['w']**3*s['s']**3*Q**18
        assert factors[2].LC() == input_top
        top = (32*Q**87*s['h']**2*(s['rho']+s['sigma'])*s['delta']*(2*s['rho']-s['delta'])
               *s['i']**2*s['f']**2*k**8*s['w']**11*s['s']**18*Ctop*(2*s['tau_gap']-k))
        actual = sp.Poly(env['polynomial'], t)
        assert actual.degree() == 135 and actual.LC() == top
        records.append(dict(B=B, cell_bits=d, scales=s, factor_degrees=FACTOR_DEGREES,
                            exact_degree=135, leading_coefficient=str(top)))
    return dict(fixtures=records,
                highest_homogeneous_term='32*(B-1)^87*h^2*(rho+sigma)*delta*(2*rho-delta)*i^2*f^2*(eta+zeta)^8*w^11*s^18*Jrep^87*C_top*(2*tau_gap-eta-zeta)',
                C_top='(B-1)*Jrep-F-Z-alpha-2*cell_bits*x')


def verify_index_recovery():
    counts = Counter()
    for A in range(3, 41):
        Delta, modulus = A*A-1, A-1
        for n in range(65):
            root, ordinate = prior.pell(A, n)
            assert ordinate % modulus == n % modulus
            if n % 2:
                assert ordinate % Delta == n % Delta
            if n >= 3 and n % 2:
                assert ordinate > n
                old_delta = (ordinate-n)//Delta
                new_delta = (ordinate-n)//modulus
                assert old_delta > 0 and new_delta == (A+1)*old_delta
                assert n+old_delta*Delta == n+new_delta*modulus == ordinate
                counts['positive_forward_inverse_coordinate_maps'] += 1
            counts['Pell_residue_cases'] += 1
        for u in range(3, modulus, 2):
            for v in range(1, modulus):
                if (prior.pell(A, v)[1]-u) % modulus == 0:
                    assert v == u
                counts['bounded_index_pairs'] += 1
    a, delta, u = sp.symbols('a delta u')
    assert sp.expand(u+delta*(a*a+4*a+3)-(u+delta*(a+3)*(a+1))) == 0
    return dict(counts, symbolic_forward_coordinate_identity=True,
                fixture_scope='Input Pell congruences and bounded-index recovery; not complete compiler zeros.')


def verify():
    return dict(source=verify_source(), degree=verify_degree(), index_recovery=verify_index_recovery())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(path.read_text()) == json.loads(json.dumps(result))
    print('linear input modulus: 89=47M+42A, 19 positive witnesses, degree135; PASS')


if __name__ == '__main__':
    main()
