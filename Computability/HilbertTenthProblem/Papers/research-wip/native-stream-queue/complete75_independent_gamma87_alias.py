"""An unresolved87 relaxation and an exact input-Pell alias mechanism.

Using sigma itself as the positive main quotient deletes gamma_sum.
Parent zeros lift positively, but the inverse may have sigma-rho<0.
The CRT component witness is outside the full compiler's q/R bounds;
this packet neither establishes nor refutes full87 universality.
"""
import argparse
from collections import Counter
import json
from math import comb, gcd, lcm
from pathlib import Path
import random

import sympy as sp

import complete75_coupled_index_linear88 as prior

eliminated = prior.eliminated
RETAINED = prior.RETAINED
FACTOR_NAMES = prior.FACTOR_NAMES
FACTOR_DEGREES = prior.FACTOR_DEGREES


def sources():
    original, old, pairs, _ = prior.sources()
    certificate = []
    for gate in old:
        if gate[0] == 'gamma_sum':
            assert gate == ('gamma_sum', '+', 'rho', 'sigma')
            continue
        if gate[0] == 'gam':
            assert gate == ('gam', '*', 'gamma_sum', 'a4m5')
            gate = ('gam', '*', 'sigma', 'a4m5')
        certificate.append(gate)
    return original, certificate, pairs, certificate+[('polynomial', '-', 'eight_units', 1)]


def verify_source():
    _, certificate, pairs, polynomial = sources()
    _, parent_certificate, parent_pairs, parent_poly = prior.sources()
    assert pairs == parent_pairs == [('eight_units', 1)]
    old = {n: (op, a, b) for n, op, a, b in parent_certificate}
    new = {n: (op, a, b) for n, op, a, b in certificate}
    assert old.keys()-new.keys() == {'gamma_sum'} and not new.keys()-old.keys()
    assert {n for n in new if new[n] != old[n]} == {'gam'}
    assert {n for n, _, a, b in parent_certificate if 'gamma_sum' in (a, b)} == {'gam'}
    available = set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, op, a, b in polynomial:
        assert name not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (a, b))
        available.add(name)
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert cc == {'M': 47, 'A': 39} and pc == {'M': 47, 'A': 40}
    rng, counts = random.Random(871511), Counter()
    for case in range(512):
        signed = case >= 384
        z = {name: rng.randrange(-9, 10) if signed else rng.randrange(1, 10)
             for name in RETAINED+['x']}
        B = rng.choice((16, 32, 64, 256))
        z.update(B=B, DC=3, DR=5, MC=B-2, MF=4,
                 cell_bits=B.bit_length()-1, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(z))
        restored = dict(z, sigma=z['sigma']-z['rho'])
        before = eliminated.run(parent_poly, eliminated.fixed_inputs(restored))
        assert all(env[n] == before[n] for n, _, _, _ in polynomial)
        assert env['R14'] == (env['wn2']+env['R12']*env['R10a']+z['sigma']*env['a4m5'])
        assert env['exponent_rhs'] == env['W']+env['R12']*env['index_rhs']+z['rho']*env['a4m5']
        parent_env = eliminated.run(parent_poly, eliminated.fixed_inputs(z))
        forward = eliminated.run(polynomial, eliminated.fixed_inputs(dict(z, sigma=z['rho']+z['sigma'])))
        assert all(forward[n] == parent_env[n] for n in (*FACTOR_NAMES, 'polynomial'))
        if not signed:
            assert z['rho']+z['sigma'] > 0
        counts['signed_cases' if signed else 'positive_cases'] += 1
        counts['nonpositive_restored_parent_sigma'] += restored['sigma'] <= 0
    return dict(certificate=dict(operations=86, multiplications=47, additions_subtractions=39,
                                 equations=1, witnesses=19),
                polynomial=dict(operations=87, multiplications=47, additions_subtractions=40,
                                exact_degree=151, witnesses=19),
                comparison=pairs, retained_positive_witnesses=RETAINED,
                polynomial_schedule=polynomial, removed_register='gamma_sum', changed_register='gam',
                signed_inverse_all_register_identities=512, forward_full_polynomial_identities=512,
                assignment_counts=dict(counts))


def verify_degree():
    t, records = sp.Symbol('t'), []
    for B, d, shift in ((16, 4, 0), (64, 6, 1), (256, 8, 2)):
        s = {name: 1+(index+shift) % 4 for index, name in enumerate(RETAINED+['x'])}
        z = {name: sp.Poly(s[name]*t+index+1, t)
             for index, name in enumerate(RETAINED+['x'])}
        z.update(B=B, DC=3, DR=5, MC=B-2, MF=4, cell_bits=d, inner_bits=3)
        env = eliminated.run(sources()[3], eliminated.fixed_inputs(z))
        assert tuple(sp.Poly(env[n], t).degree() for n in FACTOR_NAMES) == FACTOR_DEGREES
        k, Q = s['eta']+s['zeta'], (B-1)*s['Jrep']
        Ctop = Q-s['F']-s['Z']-s['alpha']-2*d*s['x']
        top = (-32*Q**99*s['h']**2*s['sigma']*s['delta']**2*s['i']**2*s['f']**2
               *k**8*s['w']**13*s['s']**20*Ctop*(2*s['tau_gap']-k))
        output = sp.Poly(env['polynomial'], t)
        assert output.degree() == 151 and output.LC() == top
        records.append(dict(B=B, scales=s, degree=151, factor_degrees=FACTOR_DEGREES,
                            leading_coefficient=str(top)))
    return dict(fixtures=records,
                highest_homogeneous_term='-32*(B-1)^99*h^2*sigma*delta^2*i^2*f^2*(eta+zeta)^8*w^13*s^20*Jrep^99*C_top*(2*tau_gap-eta-zeta)')


def pell(A, n, modulus=None):
    def multiply(x, y):
        out = tuple(sum(x[2*i+k]*y[2*k+j] for k in range(2))
                    for i in range(2) for j in range(2))
        return tuple(v % modulus for v in out) if modulus else out
    result, base = (1, 0, 0, 1), (A, A*A-1, 1, A)
    while n:
        if n % 2:
            result = multiply(result, base)
        n //= 2
        if n:
            base = multiply(base, base)
    return result[0], result[2]


def alias_index(a, u, j, period, floor):
    Delta, H = (a+2)**2-1, 4*a+3
    assert u > 0 and j > 0 and u % 2 == j % 2 == 1
    assert period > 0 and pow(2, period, H) == 1
    modulus, g = 2*Delta, gcd(2*Delta, period)
    assert (j-u) % g == 0
    reduced = period//g
    step = (((j-u)//g)*pow(modulus//g, -1, reduced)) % reduced if reduced > 1 else 0
    v = u+modulus*step
    common_period = lcm(modulus, period)
    v += max(1, (floor-v)//common_period+1)*common_period
    assert v > floor and v % modulus == u % modulus and (v-j) % period == 0
    assert v % 2 == 1 and pow(2, v, H) == pow(2, j, H)
    return v


def verify_alias_components():
    cases = 0
    for a in range(1, 17):
        A, H, Delta, R = a+2, 4*a+3, (a+2)**2-1, 7
        period = 1
        while pow(2, period, H) != 1:
            period += 1
        for u in (1, 3, 5):
            for j in (1, 3, 5):
                if u == j or (j-u) % gcd(2*Delta, period):
                    continue
                v = alias_index(a, u, j, period, max(R, u, j))
                if v > 10000:
                    continue
                mu, kappa = pell(A, v)
                D, c = pell(A, R)
                W = 1 << j
                delta, remainder = divmod(kappa-u, Delta)
                rho, rest = divmod(mu-a*kappa-W, H)
                gamma, main_rest = divmod(D-a*c-(1 << R), H)
                assert remainder == rest == main_rest == 0
                assert delta > 0 and rho > gamma > 0
                assert mu*mu-Delta*kappa*kappa == 1
                assert kappa == u+delta*Delta and mu == W+a*kappa+rho*H
                assert W != 1 << u
                cases += 1
    assert cases > 0
    return dict(materialized_positive_input_aliases=cases,
                scope='Local Pell components with a freely chosen positive parameter, not full compiler witnesses.')


def verify_fresh_main_example():
    R, d, b, x, j_input = 11, 4, 1, 1, 3
    u, X, r0 = 2*d*x+b, 1 << R, (R-1)//2
    Y = sum(comb(2*r0, r0+j)*X**j for j in range(r0+1))//2
    E, a = X*Y, Y*(X+1)
    A, Delta, H = a+2, (a+2)**2-1, 4*a+3
    P = 2*X*Y*Y+1
    tau, half_k = pell(P, (R+1)//2)
    k = 2*half_k
    D, c = pell(A, R)
    g, eta = tau-X*Y*Y*k, c-k*Y
    zeta = k-eta
    h, hrem = divmod(k-R-1, E)
    gamma, grem = divmod(D-X-a*c, H)
    assert min(g, eta, zeta, h, gamma) > 0 and hrem == grem == 0
    assert g*g+E*k*Y*(2*g-k) == 1 and D*D-Delta*c*c == 1
    assert c == k*Y+eta and k == eta+zeta == R+1+h*E
    assert c > A*Delta*Delta and c > 2*R
    period = 12288046457816218188  # Only its exact period property is required.
    assert pow(2, period, H) == 1 and gcd(2*Delta, period) == 6
    v = alias_index(a, u, j_input, period, max(R, u, j_input))
    mu_mod, kappa_mod = pell(A, v, Delta)
    assert kappa_mod == u
    mu_mod, kappa_mod = pell(A, v, H)
    assert (mu_mod-a*kappa_mod) % H == (1 << j_input) % H
    assert R < 3*16+1  # This explicit example is outside the full compiler range.
    return dict(main_index=R, X=X, Y=Y, a=a, A=A, Delta=Delta, H=H,
                main_ordinate=c, main_root=D, first_coefficient=k, first_root_gap=g,
                eta=eta, zeta=zeta, h=h, main_quotient_gamma=gamma,
                ordinary_input_component=dict(cell_bits=d, inner_bits=b, x=x, u=u),
                selected_power_index=j_input, W=1 << j_input,
                verified_power_period=period, congruence_gcd=6, input_Pell_index=v,
                full_compiler_witness=False,
                unmaterialized='Input Pell powers at v and canonical strong auxiliary powers are supplied parametrically, not expanded.',
                missing_full_interface='R=11 violates R>=3q+1 with q>=16; packed masks, transport and ordinary-input width are not instantiated.')


def verify():
    return dict(status='PASS_INDEPENDENT_GAMMA87_SCOPED_ALIAS', source=verify_source(),
                degree=verify_degree(), local_aliases=verify_alias_components(),
                fresh_main_component=verify_fresh_main_example(),
                established_universal_comparison_bound=75, established_universal_polynomial_bound=88,
                scope='Parent positive zeros lift to the87 relaxation. Conditional CRT aliases and a fresh main/input component defeat naive index recovery, but full outer87 soundness/universality is unresolved; no complete87 false-input witness is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
