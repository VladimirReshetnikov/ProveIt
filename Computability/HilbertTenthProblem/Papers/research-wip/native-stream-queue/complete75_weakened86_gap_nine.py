"""Exclude gap 2n-p=9 for complete86 zeros with R<0 and mu>0.

A uniform exact residue-size induction cuts off every one of82 low-X
compiler lanes. The remaining215 ratio domains have exact monotone
certificates; their sole ratio survivor violates the retained wrap
congruence. No source gate or positive-domain condition is changed.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path
import random

import complete75_weakened86_gap_seven as previous

parent = previous.parent
helpers = previous.helpers
pell = previous.pell
GAP = 9


def source_contract():
    return previous.source_contract()


def low_lanes():
    lanes = []
    # X+1<2^18 implies q<=63 and B in{16,32}; 64^3=2^18.
    assert 64**3 == 1 << 18
    for d in (4, 5):
        B = 1 << d
        for J in range(1, 64//(B-1)+1):
            q = (B-1)*J+1
            if q**3+1 >= 1 << 18:
                continue
            umax = 2*d*((q-2)//(2*d))+B-1
            umin = 2*d+1
            M = q*q-1
            assert (1 << umin) > q
            assert 1-M*(q-1)+M*(1 << umin)-2 > 0
            for w in range(1, ((1 << 18)-2)//q**3+1):
                X = w*q**3
                ell = (X & -X).bit_length()-1
                h = (X+1).bit_length()-1
                assert 12 <= h <= 17 and 1 << h <= X+1
                theta_upper = q**4+M*(1 << umax)+2
                A0 = 3*X*theta_upper+2*(2*q*q-3)*(X*X-1)
                A1 = 3*X
                assert X > 2*(2*q*q-3)
                cutoff = 13
                while True:
                    exponent = (h*(cutoff-9)-20)//18
                    if exponent >= 0 and 1 << exponent > max(
                            A0+A1*cutoff, cutoff, umax):
                        break
                    cutoff += 2
                assert A0+A1*cutoff > 2*A1
                assert 2*cutoff > cutoff+2
                # h>=12 gives e(p+2)>=e(p)+1 for all integers p.
                assert 2*h >= 18
                survivors = []
                for p in range(13, cutoff, 2):
                    if X >= 1 << p:
                        continue
                    power = 9*(p-ell)-8
                    if power <= 0 or (X+1)**((p+9)//2) >= 1 << power:
                        continue
                    N = ((1 << p)-X) >> ell
                    assert ((1 << p)-X) % (1 << ell) == 0
                    if N < 4*q**3*(X+1)+3:
                        continue
                    survivors.append(p)
                lanes.append(dict(d=d, B=B, J=J, q=q, w=w, X=X,
                    valuation_X=ell, floor_log2_X_plus_one=h,
                    input_index_minimum=umin, input_index_maximum=umax,
                    theta_upper_bound=theta_upper,
                    residue_constant_bound=A0, residue_linear_bound=A1,
                    large_index_cutoff=cutoff,
                    cutoff_exponent=exponent, remaining_odd_indices=survivors))
    assert len(lanes) == 82
    assert sorted({x['q'] for x in lanes}) == [16, 31, 32, 46, 61, 63]
    actual = [(x['q'], x['w'], x['remaining_odd_indices']) for x in lanes
              if x['remaining_odd_indices']]
    assert actual == [(16, 1, list(range(57, 78, 2))),
                      (31, 1, list(range(49, 96, 2))),
                      (31, 2, list(range(83, 90, 2)))]
    assert min(x['large_index_cutoff'] for x in lanes) == 65
    assert max(x['large_index_cutoff'] for x in lanes) == 141
    return lanes


def finite_domains(lanes):
    # For X=2^p, 3*(p-9)<144; odd p is at most55.
    assert 3*(57-9) == 144
    power = [(1 << t, p, 1 << (p-3*t))
             for p in range(13, 56, 2) for t in range(4, p//3+1)]
    assert len(power) == 176
    assert all(w*q**3 == 1 << p for q, p, w in power)
    low = [(x['q'], p, x['w']) for x in lanes
           for p in x['remaining_odd_indices']]
    assert len(low) == 39
    return power, low


@lru_cache(None)
def ratio_polynomials(X, p):
    n = (p+9)//2
    F = [0]*(p+9)
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


def ratio_values(X, p, Y):
    n = (p+9)//2
    c = pell(Y*(X+1)+2, p)[1]
    k = 2*pell(2*X*Y*Y+1, n)[1]
    return Y*k-c, (Y+1)*k-c


def certify_scale_triple(q, p, w):
    X, q3 = w*q**3, q**3
    U = (2*q*q-3)*pell(2, p)[1]+3*p-1
    limit = U//q3
    assert limit >= 1
    F, G = ratio_polynomials(X, p)
    cache = {}
    def at(s):
        if s not in cache:
            cache[s] = ratio_values(X, p, q3*s)
        return cache[s]
    lo, hi = 1, limit+1
    while lo < hi:
        middle = (lo+hi)//2
        if at(middle)[0] >= 0:
            hi = middle
        else:
            lo = middle+1
    last = lo-1
    points, ratio_scales = set(), []
    if last == 0:
        assert at(1)[0] >= 0
        points.add(1)
        kind = 'Lower ratio already fails at the smallest scale.'
    else:
        assert at(last)[0] < 0
        points.add(last)
        if last < limit:
            assert at(last+1)[0] >= 0
            points.add(last+1)
        if at(last)[1] <= 0:
            kind = 'Upper ratio fails at the last lower-ratio scale.'
        else:
            lo, hi = 1, last
            while lo < hi:
                middle = (lo+hi)//2
                if at(middle)[1] > 0:
                    hi = middle
                else:
                    lo = middle+1
            first = lo
            assert at(first)[1] > 0
            points.add(first)
            if first > 1:
                assert at(first-1)[1] <= 0
                points.add(first-1)
            ratio_scales = list(range(first, last+1))
            assert (q, p, w, ratio_scales) == (16, 21, 512, [2])
            kind = 'One ratio scale survives; the retained wrap congruence excludes it.'
    for s in points:
        assert (helpers.horner(F, q3*s), helpers.horner(G, q3*s)) == at(s)
    return dict(q=q, p=p, n=(p+9)//2, w=w, X=X,
                scale_multiplier_upper_bound=limit,
                last_multiplier_satisfying_lower_ratio=last,
                ratio_scale_multipliers=ratio_scales, boundary_kind=kind,
                exact_recurrence_evaluations=len(cache),
                boundary_horner_crosschecks=len(points))


def exceptional_congruence():
    q, p, n, Y = 16, 21, 15, 8192
    bp = pell(2, p)[1]
    assert bp == 296011017105 and bp % Y == 2961
    inverse = 5489
    assert 2961*inverse % Y == 1
    wrap_classes = [(-(2*n-omega*p-lam)*inverse) % Y
                    for omega in (-1, 1) for lam in (-1, 1)]
    assert wrap_classes == [1292, 4078, 2454, 5240]
    assert all(j > 509 for j in wrap_classes)
    residues = [((j*bp+2*n-omega*p-lam) % Y)
                for j in range(510) for omega in (-1, 1) for lam in (-1, 1)]
    assert len(residues) == 2040 and 0 not in residues
    return dict(q=q, p=p, n=n, X=1 << p, Y=Y, psi_2_p=bp,
                inverse_psi_residue=inverse, least_wrap_classes=wrap_classes,
                wrap_range=[0, 509], sign_pairs=4, exact_rejections=len(residues),
                minimum_nonzero_residue=min(residues),
                scope='Excludes the sole ratio survivor by a necessary full-source congruence.')


def envelope_audit(lanes):
    cases = 0
    for lane in lanes:
        h = lane['floor_log2_X_plus_one']
        A0, A1 = lane['residue_constant_bound'], lane['residue_linear_bound']
        for p in range(lane['large_index_cutoff'], lane['large_index_cutoff']+258, 2):
            e = (h*(p-9)-20)//18
            assert (h*(p+2-9)-20)//18 >= e+1
            assert 1 << e > max(A0+A1*p, p, lane['input_index_maximum'])
            assert 2*(A0+A1*p) > A0+A1*(p+2)
            cases += 1
    return dict(cases=cases, lanes=len(lanes),
                scope='Finite checks supplement the stated all-index doubling induction.')


def input_index_audit():
    roots = cases = 0
    for A in range(128, 161):
        Delta = A*A-1
        for v in range(1, A):
            value = pell(A, v)[1]
            representative = v if v % 2 else v*A
            assert 0 < representative < Delta
            assert value % Delta == representative
            roots += 1
            for u in range(9, 92):
                assert (value % Delta == u) == (v == u and v % 2 == 1)
                cases += 1
    return dict(individual_Pell_roots=roots, exact_classification_cases=cases,
                scope='Individual discriminant identities, not full candidate zeros.')


def residue_audit():
    rng = random.Random(869215)
    for case in range(640):
        draw = lambda: rng.randrange(1, 40) if case < 320 else rng.randrange(-30, 31)
        a, c, X, gamma, C, W, K, p, j = (draw() for _ in range(9))
        q = rng.choice((16, 31, 32, 46, 61, 63))
        M, u = q*q-1, rng.randrange(9, 92)
        epsilon, lam, omega = (rng.choice((-1, 1)) for _ in range(3))
        H, Delta = 4*a+3, a*a+4*a+3
        main = (X+a*c+gamma*H)**2-Delta*c*c-1
        correction = X*c-2*c*c+4*gamma*(X+a*c)+2*gamma*gamma*H
        assert 3*X*c-2*(X*X-1) == -2*main+H*correction
        R = K-M*(C-W)
        theta = K-M*C+M*(1 << u)+epsilon-lam
        wrap = R+epsilon-lam-omega*p+j*c
        L = 3*X*(theta-omega*p)+2*j*(X*X-1)
        assert 3*X*wrap-L == j*(-2*main+H*correction)+3*X*M*(W-(1 << u))
    return dict(exact_residue_corrections=640, signed_assignments=320,
                scope='Actual main/wrap correction identities off zero; no Pell extension asserted.')


def verify():
    lanes = low_lanes()
    power, low = finite_domains(lanes)
    certificates = [certify_scale_triple(*t) for t in power+low]
    assert sum(bool(c['ratio_scale_multipliers']) for c in certificates) == 1
    return dict(status='PASS_SCOPED_WEAKENED86_GAP_NINE_EXCLUSION',
        source=source_contract(), gap=9, low_X_lanes=lanes,
        finite_power_branch_triples=len(power), finite_low_branch_triples=len(low),
        scale_certificates=certificates,
        per_triple_coefficient_sign_certificates=2*len(certificates),
        distinct_coefficient_arrays=2*len({(c['X'], c['p']) for c in certificates}),
        exact_recurrence_evaluations=sum(c['exact_recurrence_evaluations'] for c in certificates),
        boundary_horner_crosschecks=sum(c['boundary_horner_crosschecks'] for c in certificates),
        exceptional_ratio_survivor=exceptional_congruence(),
        envelope_audit=envelope_audit(lanes), input_index_audit=input_index_audit(),
        residue_audit=residue_audit(),
        conclusion='Every positive candidate zero with R<0 and mu>0 has odd p and n<p<=2n-11.',
        scope='Gap9 is excluded under the unchanged complete86 compiler contract. Larger odd gaps '
              'and mu<0 remain unresolved; no universal86 bound or complete false-input zero is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    target = Path(__file__).with_suffix('.json')
    if args.write:
        target.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(target.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['conclusion'])
    print(result['scope'])
