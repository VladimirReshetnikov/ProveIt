"""Reject a same-cost 88/degree135 input-modulus shortcut.

The sole changed gate computes delta*a instead of delta*Delta.  Every
positive zero then has 2*d*x+b=psi_2(v), so each fixed instance has sparse
input projection.  No complete universal bound is improved.
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
        if gate[0] == 'index_product':
            assert gate == ('index_product', '*', 'delta', 'A')
            gate = ('index_product', '*', 'delta', 'R12')
        certificate.append(gate)
    return original, certificate, pairs, certificate+[('polynomial', '-', 'eight_units', 1)]


def manual_factors(z):
    B, J = z['B'], z['Jrep']
    q = (B-1)*J+1
    X, Y = z['w']*q**3, z['s']*q**3
    E, k = X*Y, z['eta']+z['zeta']
    c, a = k*Y+z['eta'], E+Y
    H, Delta = 4*a+3, (a+2)**2-1
    D = X+a*c+(z['rho']+z['sigma'])*H
    u = 2*z['cell_bits']*z['x']+z['inner_bits']
    C = q-z['F']-z['Z']-z['alpha']-2*z['cell_bits']*z['x']
    W, kappa = C-z['Z'], u+z['delta']*a
    mu = W+a*kappa+z['rho']*H
    K, V = Delta*(z['f']**2-1), z['o']*z['f']-c
    R = ((q*q-z['Z']-q*z['F'])*(q*q-1)
         +(z['MC']+q*(z['MF']+B-1))*J)
    index_base, g = k-z['h']*E, z['tau_gap']
    return (g*g+E*k*Y*(2*g-k), D*D-Delta*c*c,
            mu*mu-Delta*kappa*kappa,
            K*(V*V-z['y_aux']**2)+z['y_aux']**2,
            index_base-R,
            (z['DC']+B*z['DR']+X)*C+q-z['F']-z['zplus']*(q-1),
            1+(z['i']*c*c)**2-K, V-z['j']*c+index_base)


def verify_source():
    _, certificate, pairs, polynomial = sources()
    _, old, oldpairs, oldpoly = prior.sources()
    assert pairs == oldpairs == [('eight_units', 1)]
    assert len(certificate) == len(old) == 87
    changes = [(x, y) for x, y in zip(old, certificate) if x != y]
    assert changes == [(('index_product', '*', 'delta', 'A'),
                        ('index_product', '*', 'delta', 'R12'))]
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, op, left, right in polynomial:
        assert name not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert cc == {'M': 47, 'A': 40} and pc == {'M': 47, 'A': 41}
    counts, rng = Counter(), random.Random(881352)
    for case in range(512):
        signed = case >= 384
        z = {name: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
             for name in RETAINED+['x']}
        z['F'] = rng.randrange(-200, 201) if signed else rng.randrange(1, 200)
        B = rng.choice((16, 32, 64, 256))
        z.update(B=B, DC=3, DR=5, MC=B-2, MF=4,
                 cell_bits=B.bit_length()-1, inner_bits=3)
        if case % 5 == 0:
            z['zplus'] = 1
        env = eliminated.run(polynomial, eliminated.fixed_inputs(z))
        if case < 4:
            z['F'] += 2*abs(env['exponent_rhs'])+1
            env = eliminated.run(polynomial, eliminated.fixed_inputs(z))
        oldenv = eliminated.run(oldpoly, eliminated.fixed_inputs(z))
        factors = manual_factors(z)
        assert tuple(env[name] for name in FACTOR_NAMES) == factors
        product, other_product = 1, 1
        for index, factor in enumerate(factors):
            product *= factor
            if index != 2:
                other_product *= factor
                assert env[FACTOR_NAMES[index]] == oldenv[FACTOR_NAMES[index]]
        assert env['polynomial'] == product-1
        a, Delta, H = env['R12'], env['A'], env['a4m5']
        shift = z['delta']*(Delta-a)
        assert env['index_rhs'] == oldenv['index_rhs']-shift
        assert env['exponent_rhs'] == oldenv['exponent_rhs']-a*shift
        correction = (2*shift*(Delta*oldenv['index_rhs']-a*oldenv['exponent_rhs'])
                      -H*shift*shift)
        assert env['norm_input']-oldenv['norm_input'] == correction
        assert env['polynomial']-oldenv['polynomial'] == other_product*correction
        counts['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        counts['negative_computed_mu'] += env['exponent_rhs'] < 0
        counts['zero_restored_quotient'] += z['zplus'] == 1
    return dict(certificate=dict(operations=87, multiplications=47, additions_subtractions=40,
                                 equations=1, witnesses=19),
                polynomial=dict(operations=88, multiplications=47, additions_subtractions=41,
                                exact_degree=135, witnesses=19),
                changed_gate=changes, retained_positive_witnesses=RETAINED,
                comparisons=pairs, polynomial_schedule=polynomial,
                direct_full_polynomial_identities=512, parent_correction_identities=512,
                assignment_counts=dict(counts))


def verify_degree():
    t, records = sp.Symbol('t'), []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        s = {name: 1+(index+shift) % 4 for index, name in enumerate(RETAINED+['x'])}
        s['delta'], s['rho'], s['tau_gap'] = 2+shift, 5+shift, 7+shift
        z = {name: sp.Poly(s[name]*t+index+1, t)
             for index, name in enumerate(RETAINED+['x'])}
        z.update(B=B, DC=3, DR=5, MC=B-2, MF=4, cell_bits=d, inner_bits=3)
        env = eliminated.run(sources()[3], eliminated.fixed_inputs(z))
        factors = [sp.Poly(env[name], t) for name in FACTOR_NAMES]
        assert tuple(f.degree() for f in factors) == FACTOR_DEGREES
        k, Q = s['eta']+s['zeta'], (B-1)*s['Jrep']
        Ctop = Q-s['F']-s['Z']-s['alpha']-2*d*s['x']
        input_top = 4*s['delta']*(2*s['rho']-s['delta'])*s['w']**3*s['s']**3*Q**18
        assert factors[2].LC() == input_top
        top = (32*Q**87*s['h']**2*(s['rho']+s['sigma'])*s['delta']*(2*s['rho']-s['delta'])
               *s['i']**2*s['f']**2*k**8*s['w']**11*s['s']**18*Ctop*(2*s['tau_gap']-k))
        output = sp.Poly(env['polynomial'], t)
        assert output.degree() == 135 and output.LC() == top
        records.append(dict(B=B, cell_bits=d, scales=s, exact_degree=135,
                            factor_degrees=FACTOR_DEGREES, leading_coefficient=str(top)))
    return dict(fixtures=records,
                highest_homogeneous_term='32*(B-1)^87*h^2*(rho+sigma)*delta*(2*rho-delta)*i^2*f^2*(eta+zeta)^8*w^11*s^18*Jrep^87*C_top*(2*tau_gap-eta-zeta)',
                C_top='(B-1)*Jrep-F-Z-alpha-2*cell_bits*x')


def psi(A, n):
    previous, current = 0, 1
    for _ in range(n):
        previous, current = current, 2*A*current-previous
    return previous


def matrix_psi(A, n):
    def mul(x, y):
        return tuple(sum(x[2*i+k]*y[2*k+j] for k in range(2))
                     for i in range(2) for j in range(2))
    value, base = (1, 0, 0, 1), (A, A*A-1, 1, A)
    while n:
        if n % 2:
            value = mul(value, base)
        base, n = mul(base, base), n//2
    return value[2]


def verify_recovery_and_sparse_range():
    counts, examples = Counter(), []
    for a in range(2, 81):
        for v in range(33):
            value, fixed = matrix_psi(a+2, v), psi(2, v)
            assert value == psi(a+2, v)
            assert (value-fixed) % a == 0
            assert fixed % 2 == v % 2
            if v >= 2:
                assert value > fixed
                counts['positive_component_quotients'] += 1
            counts['exact_Pell_congruences'] += 1
    for R in range(7, 97):
        # The theorem gives 3a > 2^(R(R+1)/2); this inequality therefore
        # puts every psi_2(v), 1<=v<R, strictly below a.
        assert 3*4**(R-2) < 2**(R*(R+1)//2)
        for v in range(1, R):
            fixed = matrix_psi(2, v)
            assert 2**(v-1) <= fixed <= 4**(v-1)
            if v > 2:
                assert fixed < 4**(v-1)
            assert fixed <= 4**(R-2)
            counts['pretyping_representative_bounds'] += 1
    for d in range(4, 17):
        for b in (1, 3, (1 << d)-1):
            for n in (4, 8, 16, 24):
                while psi(2, n) < b or psi(2, n+1)-psi(2, n) <= 2*d:
                    n += 1
                lower, upper = psi(2, n), psi(2, n+1)
                x = (lower-b)//(2*d)+1
                u = 2*d*x+b
                assert x > 0 and lower < u < upper
                assert all(matrix_psi(2, j) != u for j in range(n+2))
                counts['explicit_rejected_inputs'] += 1
                if len(examples) < 8:
                    examples.append(dict(d=d, b=b, x=x, u=u,
                                         lower_index=n, lower=lower, upper=upper))
    for d in range(4, 13):
        for b in (1, 3, (1 << d)-1):
            for N in (16, 64, 256):
                values, v = set(), 1
                while psi(2, v) <= 2*d*N+b:
                    values.add(psi(2, v))
                    v += 1
                admitted = sum(2*d*x+b in values for x in range(1, N+1))
                bound = (2*d*N+b).bit_length()
                assert admitted <= bound
                counts['finite_sparse_range_counts'] += 1
    return dict(counts=counts, rejected_input_examples=examples,
                parametric_necessary_condition='2*d*x+b=psi_2(v) for some odd 1<=v<R',
                accepted_input_count_bound='at most 1+floor(log2(2*d*N+b)) among 1<=x<=N',
                scope='Pell components, exact omitted affine inputs and finite bound checks; no complete positive source tuple is claimed')


def verify():
    return dict(status='PASS_ZERO_OFFSET_INPUT_MODULUS_OBSTRUCTION',
                source=verify_source(), degree=verify_degree(),
                obstruction=verify_recovery_and_sparse_range(),
                established_universal_polynomial_bound=88,
                established_universal_comparison_bound=75,
                conclusion='The altered 88/degree135 source has sparse positive input projection for every fixed admissible compiler tuple. It cannot represent all positive integers; it is not a new universal bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'], result['source']['polynomial'])
