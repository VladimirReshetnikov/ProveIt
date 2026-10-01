"""Exact exclusion of gap 2n-p=5 in the negative-R, positive-mu branch.

The exact main-root residue first forces X=2**p.  Forty remaining
dyadic-q triples receive complete coefficient-sign/endpoint certificates.
No arithmetic gate of the unresolved86 candidate is changed.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

import complete75_weakened86_gap_three as previous

parent = previous.parent
pell = previous.pell


def finite_bounds():
    # If X<2**p, the main-root congruence forces H<=2**p-X.
    # Ratio growth would then give (X+1)**((p+5)//2)<2**(5*p-4),
    # whereas X>=4096 gives a strict lower bound 2**(6*p+30).
    assert 6*13+30 > 5*13-4
    # If X=2**p, q**3 divides X, so q=2**t and w=2**(p-3*t).
    # Cubing the width/growth bound gives 3*p*(p-5)/2<40*p.
    # The first excluded odd index is33; the gap only increases.
    assert 3*(33-5) >= 80
    triples = []
    for p in range(13, 32, 2):
        b = pell(2, p)[1]
        assert b <= 4**(p-1)
        for t in range(4, p//3+1):
            q, w = 1 << t, 1 << (p-3*t)
            assert w*q**3 == 1 << p
            # B=q,J=1 is an admissible compiler representation; other
            # representations of this same q do not change the tests.
            assert q == ((1 << t)-1)*1+1
            triples.append((q, p, w))
    assert len(triples) == 40
    return triples, dict(main_root_forces='X=2^p', p_minimum=13,
                         p_maximum=31, p_odd=True,
                         q_exponents='4<=t<=floor(p/3)',
                         scale_triples=len(triples),
                         distinct_ratio_polynomial_pairs=10)


@lru_cache(None)
def ratio_polynomials(p):
    X, n = 1 << p, (p+5)//2
    F = [0]*(p+5)
    for i, coefficient in enumerate(previous.shifted_psi_coefficients(2, p)):
        F[i] = -coefficient*(X+1)**i
    K = [2*a*(2*X)**i
         for i, a in enumerate(previous.shifted_psi_coefficients(1, n))]
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
    X, n = 1 << p, (p+5)//2
    c = pell(Y*(X+1)+2, p)[1]
    k = 2*pell(2*X*Y*Y+1, n)[1]
    return Y*k-c, (Y+1)*k-c


def certify_scale_triple(q, p, w):
    assert w*q**3 == 1 << p
    q3 = q**3
    U = (2*q*q-3)*pell(2, p)[1]+3*p-1
    limit = U//q3
    assert limit >= 1
    F, G = ratio_polynomials(p)
    cache = {}
    def at(multiplier):
        if multiplier not in cache:
            cache[multiplier] = ratio_values(p, q3*multiplier)
        return cache[multiplier]
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
        kind = 'Lower ratio fails at the smallest positive multiplier.'
    else:
        assert at(last)[0] < 0
        if last < limit:
            assert at(last+1)[0] >= 0
        assert at(last)[1] <= 0
        points = (last,) if last == limit else (last, last+1)
        kind = 'Upper ratio fails at the largest multiplier satisfying the lower ratio.'
    for s in points:
        assert (previous.horner(F, q3*s), previous.horner(G, q3*s)) == at(s)
    return dict(q=q, p=p, n=(p+5)//2, w=w, X=1 << p,
                scale_multiplier_upper_bound=limit,
                last_multiplier_satisfying_lower_ratio=last,
                boundary_kind=kind, ratio_solution_exists=False,
                exact_recurrence_evaluations=len(cache),
                boundary_horner_crosschecks=len(points))


def main_root_residue_audit():
    # These are exact individual Pell roots, not full candidate zeros.
    cases = 0
    for q in (16, 31, 32, 46):
      for w in (1, 2, 7):
       for s in (1, 3, 8):
        X, Y = w*q**3, s*q**3
        a = Y*(X+1)
        A, H = a+2, 4*a+3
        assert 0 < X < H
        for p in range(13, 34, 2):
            chi, psi = pell(A, p)
            root = chi-a*psi
            assert (root-pow(2, p, H)) % H == 0
            if (X-(1 << p)) % H == 0:
                assert X <= 1 << p
                if X < 1 << p:
                    assert H <= (1 << p)-X
            cases += 1
    return dict(cases=cases,
                scope='Individual exact main Pell roots only; no complete candidate zeros asserted.')


def discarded_coarse_bound_family():
    # A regression shows why replacing the exact main-root congruence by
    # its weaker inequality X<=2**p would leave this proof incomplete.
    # The note proves the displayed family for every odd p>=13.
    cases = 0
    for p in range(13, 514, 2):
        q, X = 16, 4096
        Y = 1 << ((3*p-15)//2)
        b = pell(2, p)[1]
        U = (2*q*q-3)*b+3*p-1
        assert Y % q**3 == 0 and Y >= q**3
        assert X <= 1 << p and Y <= U
        assert (X+1)**((p-5)//2) < 32*Y**4*(Y+1)
        H = 4*Y*(X+1)+3
        assert H > 1 << p and X < 1 << p
        assert (X-(1 << p)) % H != 0
        cases += 1
    return dict(cases=cases, q=16, X=4096,
                Y_formula='2^((3p-15)/2)',
                scope='Coarse-growth/width survivors, all rejected by the exact main-root residue; '
                      'neither both strict ratios nor full candidate zeros are asserted.')


def verify():
    triples, bounds = finite_bounds()
    certificates = [certify_scale_triple(*triple) for triple in triples]
    assert not any(row['ratio_solution_exists'] for row in certificates)
    return dict(status='PASS_SCOPED_WEAKENED86_GAP_FIVE_EXCLUSION',
                source=parent.source_contract(), finite_bounds=bounds,
                scale_certificates=certificates,
                coefficient_sign_certificates=2*len(certificates),
                distinct_coefficient_arrays=20,
                exact_recurrence_evaluations=sum(r['exact_recurrence_evaluations'] for r in certificates),
                boundary_horner_crosschecks=sum(r['boundary_horner_crosschecks'] for r in certificates),
                main_root_residue_audit=main_root_residue_audit(),
                discarded_coarse_bound_family=discarded_coarse_bound_family(),
                conclusion='Every positive candidate zero with R<0 and mu>0 has odd p and n<p<=2n-7.',
                scope='Exact exclusion of the complete necessary gap5 domain. Larger odd gaps and mu<0 '
                      'remain unresolved. The86 candidate is not promoted to a universal bound.')


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
