"""Exclude gap 2n-p=7 at positive86 zeros with R<0 and mu>0.

Ninety-six finite X=2**p cases have exact ratio certificates. The three
remaining low-X lanes are excluded uniformly using the actual input
congruence and a main-norm/wrap residue whose size is smaller than H.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path
import random

import complete75_weakened86_gap_five as previous

parent = previous.parent
helpers = previous.previous
pell = previous.pell


def source_contract():
    contract = parent.source_contract()
    rows = {n: (op, a, b) for n, op, a, b in parent.candidate.sources()[3]}
    critical = dict(
        scaled_t=('*', 'twice_cell_bits', 'x'),
        marked_rhs=('-', 'C_after_alpha', 'scaled_t'),
        W=('-', 'marked_rhs', 'Z'),
        odd_index=('+', 'scaled_t', 'inner_bits'),
        index_product=('*', 'delta', 'A'),
        index_rhs=('+', 'odd_index', 'index_product'),
        difference_multiple=('*', 'index_rhs', 'R12'),
        exponent_partial=('+', 'W', 'difference_multiple'),
        modulus_multiple=('*', 'rho', 'a4m5'),
        exponent_rhs=('+', 'exponent_partial', 'modulus_multiple'),
        mu2=('*', 'exponent_rhs', 'exponent_rhs'),
        kappa2=('*', 'index_rhs', 'index_rhs'),
        scaled_kappa2=('*', 'A', 'kappa2'),
        norm_input=('-', 'mu2', 'scaled_kappa2'))
    assert all(rows[n] == row for n, row in critical.items())
    return dict(contract, additional_input_rows_checked=len(critical))


def finite_bounds():
    # X=2**p gives 3*(p-7)<112; the first excluded odd index is45.
    assert 3*(45-7) >= 112
    triples = [(1 << t, p, 1 << (p-3*t))
               for p in range(13, 44, 2) for t in range(4, p//3+1)]
    assert len(triples) == 96
    assert all(w*q**3 == 1 << p for q, p, w in triples)
    # Otherwise X+1<2**14. The compiler relation forces B=q=16,J=1.
    low = []
    for d in range(4, 15):
        B = 1 << d
        for J in range(1, 26):
            q = (B-1)*J+1
            if q**3 >= (1 << 14)-1:
                continue
            for w in range(1, (1 << 14)//q**3+1):
                if w*q**3+1 < 1 << 14:
                    low.append(dict(B=B, J=J, q=q, w=w, X=w*q**3))
    assert low == [dict(B=16, J=1, q=16, w=w, X=4096*w) for w in (1, 2, 3)]
    assert 26**3 > (1 << 14)-1
    return triples, dict(finite_branch='X=2^p', p_minimum=13, p_maximum=43,
                         p_odd=True, q_exponents='4<=t<=floor(p/3)',
                         scale_triples=96, low_X_lanes=low,
                         low_X_ordinary_input=1, low_X_p_minimum=133)


@lru_cache(None)
def ratio_polynomials(p):
    X, n = 1 << p, (p+7)//2
    F = [0]*(p+7)
    for i, coefficient in enumerate(helpers.shifted_psi_coefficients(2, p)):
        F[i] = -coefficient*(X+1)**i
    K = [2*a*(2*X)**i
         for i, a in enumerate(helpers.shifted_psi_coefficients(1, n))]
    for i, coefficient in enumerate(K):
        F[2*i+1] += coefficient
    G = F.copy()
    for i, coefficient in enumerate(K):
        G[2*i] += coefficient
    for coefficients in (F, G):
        assert all(c < 0 for c in coefficients[:p])
        assert all(c >= 0 for c in coefficients[p:])
        assert coefficients[-1] > 0
    return tuple(F), tuple(G)


def ratio_values(p, Y):
    X, n = 1 << p, (p+7)//2
    c = pell(Y*(X+1)+2, p)[1]
    k = 2*pell(2*X*Y*Y+1, n)[1]
    return Y*k-c, (Y+1)*k-c


def certify_scale_triple(q, p, w):
    assert w*q**3 == 1 << p
    U = (2*q*q-3)*pell(2, p)[1]+3*p-1
    q3, limit = q**3, U//q**3
    assert limit >= 1
    F, G = ratio_polynomials(p)
    cache = {}
    def at(s):
        if s not in cache:
            cache[s] = ratio_values(p, s*q3)
        return cache[s]
    lo, hi = 1, limit+1
    while lo < hi:
        middle = (lo+hi)//2
        if at(middle)[0] >= 0:
            hi = middle
        else:
            lo = middle+1
    last = lo-1
    if last == 0:
        assert at(1)[0] >= 0
        points = (1,)
        kind = 'Lower ratio fails at the smallest scale.'
    else:
        assert at(last)[0] < 0 and at(last)[1] <= 0
        if last < limit:
            assert at(last+1)[0] >= 0
        points = (last,) if last == limit else (last, last+1)
        kind = 'Upper ratio fails at the last scale satisfying the lower ratio.'
    for s in points:
        assert (helpers.horner(F, q3*s), helpers.horner(G, q3*s)) == at(s)
    return dict(q=q, p=p, n=(p+7)//2, w=w, X=1 << p,
                scale_multiplier_upper_bound=limit,
                last_multiplier_satisfying_lower_ratio=last,
                boundary_kind=kind, ratio_solution_exists=False,
                exact_recurrence_evaluations=len(cache),
                boundary_horner_crosschecks=len(points))


def low_X_bounds():
    # The proof is an exact exponent comparison, not a numerical logarithm.
    assert all(6*p+42 >= 7*p-90 for p in range(13, 133, 2))
    assert (1 << 66) > (1 << 48)+(1 << 16)*133
    assert 1-255*15+255*(1 << 9)-2 > 0
    assert (1 << 16)+255*(1 << 23)+2 < 1 << 31
    growth_cases = 0
    for p in range(133, 1026, 2):
        assert 6*p-50 > 7*((p-1)//2)
        assert (1 << ((p-1)//2)) > p
        assert (1 << ((p-1)//2)) > (1 << 48)+(1 << 16)*p
        growth_cases += 1
    # Every residue wrap permitted by the inherited bound is covered.
    wrap_cases = 0
    for X in (4096, 8192, 12288):
        for j in range(510):
            assert ((2*j) % X == 0) == (j == 0)
            wrap_cases += 1
    theta_cases = 0
    minimum = None
    maximum = 0
    masks = [(MC, MF) for MC in range(1, 15) for MF in range(1, 15)
             if MC % 4 == 2 and MF % 8 == 4 and MC.bit_count()+MF.bit_count() == 4]
    assert masks == [(6, 12), (10, 12), (14, 4)]
    for MC, MF in masks:
     for F in range(1, 8):
      for alpha in range(1, 9-F):
        C = 8-F-alpha
        K = 16*(16-F)*255+MC+16*(MF+15)
        assert 0 <= C <= 6 and 0 < K < 1 << 16
        for u in range(9, 24):
         for epsilon in (-1, 1):
          for lam in (-1, 1):
            theta = K-255*C+255*(1 << u)+epsilon-lam
            assert 0 < theta < 1 << 31
            minimum = theta if minimum is None else min(minimum, theta)
            maximum = max(maximum, theta)
            theta_cases += 1
    return dict(growth_envelope_cases=growth_cases, wrap_divisibility_cases=wrap_cases,
                theta_cases=theta_cases, minimum_fixture_theta=minimum,
                maximum_fixture_theta=maximum,
                scope='Integer envelope/allowed-mask consequences; no full candidate zero is constructed.')


def input_index_audit():
    roots = classifications = 0
    for A in range(25, 97):
        Delta = A*A-1
        for v in range(1, A):
            c = pell(A, v)[1]
            representative = v if v % 2 else v*A
            assert 0 < representative < Delta
            assert c % Delta == representative
            roots += 1
            for u in range(9, 24):
                assert (c % Delta == u) == (v == u and v % 2 == 1)
                classifications += 1
    return dict(individual_Pell_roots=roots, discriminant_classifications=classifications,
                scope='Exact discriminant input-index checks; arbitrary A fixtures are not candidate zeros.')


def combined_residue_identity():
    rng = random.Random(867133)
    signed = 0
    for case in range(512):
        draw = lambda: rng.randrange(1, 30) if case < 256 else rng.randrange(-20, 21)
        a, c, X, gamma, C, W, K, p, j = (draw() for _ in range(9))
        u = rng.randrange(1, 24)
        epsilon, lam, omega = (rng.choice((-1, 1)) for _ in range(3))
        H, Delta, M = 4*a+3, a*a+4*a+3, 255
        D = X+a*c+gamma*H
        main_residual = D*D-Delta*c*c-1
        correction = X*c-2*c*c+4*gamma*(X+a*c)+2*gamma*gamma*H
        assert 3*X*c-2*(X*X-1) == -2*main_residual+H*correction
        Z = C-W
        R = K-M*Z
        theta = K-M*C+M*(1 << u)+epsilon-lam
        wrap_residual = R+epsilon-lam-omega*p+j*c
        L = 3*X*(theta-omega*p)+2*j*(X*X-1)
        assert 3*X*wrap_residual-L == (
            j*(-2*main_residual+H*correction)+3*X*M*(W-(1 << u)))
        signed += case >= 256
    return dict(exact_full_residue_identities=512, signed_cases=signed,
                scope='Exact algebraic correction identities on arbitrary assignments, not native Pell zeros.')


def verify():
    triples, bounds = finite_bounds()
    certificates = [certify_scale_triple(*triple) for triple in triples]
    assert not any(r['ratio_solution_exists'] for r in certificates)
    return dict(status='PASS_SCOPED_WEAKENED86_GAP_SEVEN_EXCLUSION',
        source=source_contract(), branch_bounds=bounds, scale_certificates=certificates,
        per_triple_coefficient_sign_certificates=192, distinct_coefficient_arrays=32,
        exact_recurrence_evaluations=sum(r['exact_recurrence_evaluations'] for r in certificates),
        boundary_horner_crosschecks=sum(r['boundary_horner_crosschecks'] for r in certificates),
        low_X_envelopes=low_X_bounds(), input_index_audit=input_index_audit(),
        combined_residue_identity=combined_residue_identity(),
        conclusion='Every positive candidate zero with R<0 and mu>0 has odd p and n<p<=2n-9.',
        scope='Complete exclusion of gap7 under the unchanged86 compiler contract. Larger odd gaps '
              'and mu<0 remain unresolved; no universal86 bound or complete false-input zero is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['conclusion'])
    print(result['scope'])
