"""Exact input-extension criterion for the unresolved independent-gamma87 source.

This does not produce a complete false-input witness or a new universal bound.
It audits both parity branches, source-preserving width transport, and a
uniform ternary-index obstruction on genuine half-binomial parameters.
"""
import argparse
from math import comb, gcd, lcm
import json
from pathlib import Path
import random

import complete75_independent_gamma87_alias as parent


def order_two(H):
    assert H > 1 and H % 2
    z, order = 2 % H, 1
    while z != 1:
        z = 2*z % H
        order += 1
    return order


def valuation(n, p):
    assert n > 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def crt_lift(residue, modulus, j, period, floor):
    g = gcd(modulus, period)
    if (j-residue) % g:
        return None
    reduced = period//g
    step = (((j-residue)//g)*pow(modulus//g, -1, reduced)) % reduced if reduced > 1 else 0
    v = residue+modulus*step
    common = lcm(modulus, period)
    v += max(0, (floor-v)//common+1)*common
    assert v > floor and (v-residue) % modulus == (v-j) % period == 0
    return v


def criterion(a, u, W):
    """Least-order criterion with mu>0; small-parameter audit implementation."""
    assert a > 0 and a % 6 == 0 and u > 0 and u % 2
    A, Delta, H = a+2, (a+2)**2-1, 4*a+3
    O = order_two(H)
    logs = {pow(2, j, H): j for j in range(O)}
    j = logs.get(W % H)
    g = gcd(2*Delta, O)
    branches = [] if j is None else [parity for parity, residue in ((1, u), (0, A*u))
                                    if (j-residue) % g == 0]
    assert len(branches) <= 1  # 3|H makes O and g even.
    return O, g, j, branches


def exhaustive_periods():
    """Direct Pell recurrence over the whole joint period, not CRT enumeration."""
    fixtures, steps, comparisons = [], 0, 0
    for a in range(6, 73, 6):
        A, Delta, H = a+2, (a+2)**2-1, 4*a+3
        O = order_two(H)
        joint = lcm(2*Delta, O)
        us = tuple(range(1, min(a+1, 16), 2))
        observed = {u: set() for u in us}
        modulus = lcm(Delta, H)
        chi, psi, power = 1, 0, 1
        for v in range(joint):
            assert (chi-a*psi) % H == power
            u = psi % Delta
            if u in observed:
                observed[u].add(power)
            chi, psi = (A*chi+Delta*psi) % modulus, (chi+A*psi) % modulus
            power = 2*power % H
        assert psi % Delta == 0 and power == 1
        for u in us:
            predicted = {W for W in range(H) if criterion(a, u, W)[3]}
            assert predicted == observed[u]
            assert all(W % 3 != 0 for W in predicted)
            comparisons += H
        steps += joint
        fixtures.append(dict(a=a, H=H, Delta=Delta, order=O,
                             gcd=gcd(2*Delta, O), joint_period=joint,
                             tested_odd_indices=list(us)))
    return dict(direct_recurrence_steps=steps, residue_comparisons=comparisons,
                fixtures=fixtures, scope='Small free parameters; not compiled histories.')


def positive_extensions():
    cases, branches, signed_representatives = 0, {0: 0, 1: 0}, 0
    for a in (6, 12, 18, 24):
        A, Delta, H = a+2, (a+2)**2-1, 4*a+3
        for u in (1, 3, 5):
            O = order_two(H)
            for j in range(O):
                W = pow(2, j, H)
                if j % 2:
                    W -= H
                _, g, actual_j, accepted = criterion(a, u, W)
                for parity in accepted:
                    residue = u if parity else A*u
                    v = crt_lift(residue, 2*Delta, actual_j, O, max(u, abs(W), 7))
                    assert v is not None and v % 2 == parity
                    mu, kappa = parent.pell(A, v)
                    delta, dr = divmod(kappa-u, Delta)
                    rho, rr = divmod(mu-a*kappa-W, H)
                    assert dr == rr == 0 and delta > 0 and rho > 0
                    assert mu*mu-Delta*kappa*kappa == 1
                    assert kappa == u+delta*Delta and mu == W+a*kappa+rho*H
                    cases += 1
                    branches[parity] += 1
                    signed_representatives += W < 0
    return dict(materialized_positive_extensions=cases, parity_counts=branches,
                negative_W_cases=signed_representatives,
                scope='Input components only; no complete outer tuple is claimed.')


def negative_root_scope_fixture():
    a, u, delta, rho, W = 12, 3, 4, 1, -20381
    A, Delta, H = a+2, (a+2)**2-1, 4*a+3
    kappa = u+delta*Delta
    mu = W+a*kappa+rho*H
    assert (kappa, mu) == (783, -10934)
    assert mu*mu-Delta*kappa*kappa == 1
    assert parent.pell(A, 3) == (-mu, kappa)
    assert W % H == 19 and not criterion(a, u, W)[3]
    return dict(a=a, u=u, delta=delta, rho=rho, W=W, kappa=kappa, mu=mu,
                scope='Outside genuine width: negative-root example disproves an unrestricted-W converse without mu>0.')


def no_ternary_two(n):
    while n:
        n, digit = divmod(n, 3)
        if digit == 2:
            return False
    return True


def native_a_mod27(R):
    """Evaluate the actual half-binomial formula modulo54 before division by2."""
    r, modulus = (R-1)//2, 54
    X = pow(2, R, modulus)
    numerator = sum(comb(2*r, r+j)*pow(X, j, modulus) for j in range(r+1)) % modulus
    assert numerator % 2 == 0
    return (numerator//2)*(X+1) % 27


def ternary_obstruction():
    native, local, prime_period = [], 0, 0
    for R in range(3, 1024, 4):
        r = (R-1)//2
        a27 = native_a_mod27(R)
        is_class = r % 3 == 0 and no_ternary_two(r)
        assert a27 % 9 in (0, 6)
        assert (a27 % 9 == 6) == is_class
        # Independent direct alternating-binomial identity and Lucas residue.
        lhs = sum((-1)**j*comb(2*r, r+j) for j in range(r+1))
        assert 2*lhs == comb(2*r, r)
        assert comb(2*r, r) % 3 == (2 if no_ternary_two(r) else 0)
        native.append(dict(R=R, a_mod27=a27, excluded_mod3_input_classes=is_class))
    for a in range(6, 6001, 6):
        if a % 9 == 3:
            continue  # This residue does not occur in the genuine formula.
        Delta, H = (a+2)**2-1, 4*a+3
        d3, e3 = valuation(Delta, 3), valuation(H, 3)
        h = min(d3, e3-1)
        expected = 0 if a % 9 == 0 else 2 if a % 27 == 6 else 1
        assert h == expected
        period = 2*3**(e3-1)
        assert order_two(3**e3) == period
        assert gcd(2*Delta, period) == 2*3**h
        local += 1
    # Numerical main-kernel range and divisibility prerequisites can coexist
    # with the ternary class. This is NOT an actual packed compiler history.
    R, t = 491515, 5
    q, r = 1 << t, (R-1)//2
    assert q >= 16 and R % 4 == 3 and 3*q+1 <= R < q**4
    assert R.bit_count() >= 3*t+2 and r % 3 == 0 and no_ternary_two(r)
    for a in range(18, 18001, 18):
        p = (4*a+3)//3
        if p > 1 and all(p % divisor for divisor in range(2, int(p**0.5)+1)):
            period = p-1
            Delta, H = (a+2)**2-1, 4*a+3
            assert pow(2, period, H) == 1 and gcd(2*Delta, period) == 6
            assert gcd(2*Delta, order_two(H)) in (2, 6)
            prime_period += 1
    return dict(native_formula_checks=len(native), native_fixtures=native,
                local_three_power_checks=local,
                range_only_class_example=dict(R=R, q=q, popcount=R.bit_count(),
                                              full_compiler_history=False),
                conditional_H_equals_3prime_checks=prime_period,
                scope='The class theorem applies to actual histories when its index condition holds; examples do not instantiate outer compiler constraints.')


def source_transport():
    _, certificate, _, polynomial = parent.sources()
    consumers = lambda name: [gate[0] for gate in certificate if name in gate[2:]]
    assert consumers('x') == ['scaled_t']
    assert consumers('alpha') == ['C_after_alpha']
    assert consumers('scaled_t') == ['marked_rhs', 'odd_index']
    assert consumers('delta') == ['index_product']
    assert consumers('rho') == ['modulus_multiple']
    stable_factors = tuple(n for n in parent.FACTOR_NAMES if n != 'norm_input')
    stable_registers = ('q', 'wn2', 'sn2', 'R12', 'A', 'a4m5', 'marked_rhs',
                        'W', 'r_lhs', 'R10a', 'R14')
    rng, cases = random.Random(872026), 0
    for _ in range(512):
        z = {n: rng.randrange(-8, 9) for n in parent.RETAINED+['x']}
        d = rng.choice((4, 5, 6, 8))
        B = 1 << d
        z.update(B=B, DC=3, DR=5, MC=B-2, MF=4,
                 cell_bits=d, inner_bits=3)
        shift = rng.randrange(-5, 6)
        changed = dict(z, x=z['x']+shift, alpha=z['alpha']-2*d*shift,
                       delta=rng.randrange(-12, 13), rho=rng.randrange(-12, 13))
        old = parent.eliminated.run(polynomial, parent.eliminated.fixed_inputs(z))
        new = parent.eliminated.run(polynomial, parent.eliminated.fixed_inputs(changed))
        assert all(old[n] == new[n] for n in stable_registers+stable_factors)
        assert new['odd_index'] == old['odd_index']+2*d*shift
        product = 1
        for factor in stable_factors:
            product *= old[factor]
        assert new['polynomial'] == product*new['norm_input']-1
        cases += 1
    return dict(signed_full_source_transport_identities=cases,
                unchanged_factors=stable_factors, unchanged_outer_main_registers=stable_registers,
                audited_consumers={n: consumers(n) for n in ('x', 'alpha', 'scaled_t', 'delta', 'rho')},
                scope='All-assignment identities only. Positive zeros require the proved parent history and CRT hypotheses.')


def verify():
    return dict(status='PASS_EXACT_GAMMA87_INPUT_PERIOD_CRITERION',
                source_transport=source_transport(),
                full_period_audit=exhaustive_periods(),
                positive_components=positive_extensions(),
                negative_root_scope=negative_root_scope_fixture(),
                ternary_class=ternary_obstruction(),
                complete87_false_input_witness=False,
                established_universal_polynomial_bound=88,
                scope='Exact fixed-history input extension criterion and uniform obstruction class; full87 universality remains unresolved.')


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
