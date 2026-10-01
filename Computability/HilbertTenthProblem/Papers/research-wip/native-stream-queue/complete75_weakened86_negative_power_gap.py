"""Finite power-X reduction for the unchanged86 negative-input branch.

For X=2**p, prove a scale bound independent of the input Pell index and
exclude every odd gap through17. Low-X data and larger gaps remain open.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import complete75_weakened86_gap_eleven as parent
import complete75_weakened86_negative_input_residues as residues

pell = parent.pell
GAPS = (1, 3, 5, 7, 9, 11, 13, 15, 17)


def finite_domains(gap):
    """All necessary power-X triples for a fixed odd gap, not full zeros."""
    assert gap >= 1 and gap % 2
    return [(1 << t, p, 1 << (p-3*t))
            for p in range(max(13, gap+2), 7*gap, 2)
            if 3*p*p-19*gap*p < 12*gap+6
            for t in range(4, p//3+1)]


@lru_cache(None)
def ratio_polynomials(gap, p):
    X, n = 1 << p, (p+gap)//2
    F = [0]*(p+gap)
    for i, coefficient in enumerate(parent.helpers.shifted_psi_coefficients(2, p)):
        F[i] = -coefficient*(X+1)**i
    K = [2*a*(2*X)**i for i, a in enumerate(parent.helpers.shifted_psi_coefficients(1, n))]
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


def ratio_values(gap, p, Y):
    X, n = 1 << p, (p+gap)//2
    c = pell(Y*(X+1)+2, p)[1]
    k = 2*pell(2*X*Y*Y+1, n)[1]
    return Y*k-c, (Y+1)*k-c


def certify_domain(gap, q, p, w):
    X, M, q3 = 1 << p, q*q-1, q**3
    assert w*q3 == X
    # The new negative-input theorem gives Y<2MX^2, not the older
    # positive-input upper bound involving psi_2(p).
    bound = 2*M*X*X
    limit = (bound-1)//q3
    assert limit >= 1
    F, G = ratio_polynomials(gap, p)
    cache = {}
    def at(s):
        if s not in cache:
            cache[s] = ratio_values(gap, p, s*q3)
        return cache[s]
    if at(1)[0] >= 0:
        last = 0
    else:
        lo, hi = 1, 2
        while hi <= limit and at(hi)[0] < 0:
            lo, hi = hi, 2*hi
        hi = min(hi, limit+1)
        while hi-lo > 1:
            middle = (lo+hi)//2
            if at(middle)[0] >= 0:
                hi = middle
            else:
                lo = middle
        last = lo
    points, solutions = ({1} if last == 0 else {last}), []
    if last:
        assert at(last)[0] < 0
        if last < limit:
            assert at(last+1)[0] >= 0
            points.add(last+1)
        if at(last)[1] > 0:
            lo, hi = 1, last
            while lo < hi:
                middle = (lo+hi)//2
                if at(middle)[1] > 0:
                    hi = middle
                else:
                    lo = middle+1
            first = lo
            points.add(first)
            assert at(first)[1] > 0
            if first > 1:
                assert at(first-1)[1] <= 0
                points.add(first-1)
            solutions = list(range(first, last+1))
            assert (gap, q, p, solutions) == (9, 16, 21, [2])
    for s in points:
        assert tuple(parent.helpers.horner(cs, q3*s) for cs in (F, G)) == at(s)
    return dict(gap=gap, q=q, p=p, n=(p+gap)//2, w=w, X=X,
        strict_scale_bound=bound, scale_multiplier_limit=limit,
        last_lower_ratio_multiplier=last, surviving_ratio_multipliers=solutions,
        coefficient_sign_certificate=True,
        coefficient_sha256=hashlib.sha256(json.dumps([F, G]).encode()).hexdigest(),
        exact_Pell_evaluations=len(cache), boundary_Horner_checks=len(points))


def envelope_audit():
    cases = 0
    for p in range(13, 302, 2):
      X = 1 << p
      for t in range(4, p//3+1):
        q, M = 1 << t, (1 << (2*t))-1
        assert q**3 <= X and 8*M < X
        assert q**4+p+2 < 2*M*X
        # Uniform positive lower bound for L in the F_r case with j>=1.
        assert 2*(X*X-1)-3*X*(p+2) > 3*X*M
        assert 6*M*X**3+3*M*X < 8*M*X**3
        assert 27*M*X*X < 16*M*X**3
        assert 17*M*X*X < 8*M*X**3
        cases += 1
    cutoffs = []
    for gap in (1, 3, 13, 51, 101, 1001):
        # Quadratic is increasing once p>=7g; the displayed first point
        # and positive derivative verify that the finite range is safe.
        p = max(13, 7*gap)
        assert 3*p*p-19*gap*p >= 12*gap+6
        assert 6*p-19*gap > 0
        cutoffs.append([gap, p])
    return dict(power_envelope_cases=cases, large_gap_cutoff_examples=cutoffs,
        scope='Finite checks of bounds proved uniformly in the note, not full candidate zeros.')


def residue_audit():
    rng = random.Random(86131067)
    cases = signed = 0
    for p in (13, 15, 17, 21):
      X = 1 << p
      for t in range(4, p//3+1):
       q, M = 1 << t, (1 << (2*t))-1
       for scale in (1, 2, 5):
        Y = scale*q**3
        a, A, H = Y*(X+1), Y*(X+1)+2, 4*Y*(X+1)+3
        chi, c = pell(A, p)
        gamma, rem = divmod(chi-a*c-X, H)
        assert rem == 0 and gamma >= 2
        assert 3*X*c % H == 2*(X*X-1) % H
        assert c > q**4+p+2
        frs = residues.canonical_input_residues(A, p)
        for r, fr in enumerate(frs):
          if r < p:
            assert ((1 << r)*fr-1) % H == 0
          elif r > p:
            s = 2*p-r
            assert (fr-(1 << s)) % H == 0
            assert fr >= 1 << s
          else:
            assert (fr-X+c) % H == 0
          for is_signed in (False, True):
            draw = lambda: rng.randrange(-30, 31) if is_signed else rng.randrange(1, 31)
            theta, j, rho = draw(), draw(), draw()
            wrap = M*(H*rho+fr)-theta-j*c
            if r < p:
                L = 3*X*(theta*(1 << r)-M)+2*j*(X*X-1)*(1 << r)
                assert (L+3*X*(1 << r)*wrap) % H == 0
            elif r > p:
                L = 3*X*(M*(1 << (2*p-r))-theta)-2*j*(X*X-1)
                assert (L-3*X*wrap) % H == 0
            else:
                L = 3*X*(M*X-theta)-2*(M+j)*(X*X-1)
                assert (L-3*X*wrap) % H == 0
            cases += 1
            signed += is_signed
    return dict(exact_main_and_wrap_residue_cases=cases, signed_cases=signed,
        scope='Actual main-residue algebra; these hosts need not meet first/main ratios or full equations.')


def verify():
    certificates = [certify_domain(g, *triple) for g in GAPS for triple in finite_domains(g)]
    counts = {str(g): sum(c['gap'] == g for c in certificates) for g in GAPS}
    assert counts == {'1': 0, '3': 8, '5': 40, '7': 96, '9': 192, '11': 300, '13': 431, '15': 613, '17': 795}
    exceptional = residues.actual_ratio_tuple_exclusion()
    assert [(c['gap'], c['q'], c['p'], c['surviving_ratio_multipliers'])
            for c in certificates if c['surviving_ratio_multipliers']] == [(9, 16, 21, [2])]
    exceptional_summary = {k: v for k, v in exceptional.items() if k != 'exact_interval_certificates'}
    exceptional_summary['interval_receipt_sha256'] = hashlib.sha256(
        json.dumps(exceptional['exact_interval_certificates']).encode()).hexdigest()
    return dict(status='PASS_SCOPED_NEGATIVE_POWER_GAP_REDUCTION',
        source=parent.source_contract(), finite_domain_counts=counts,
        certificates=certificates, per_domain_sign_certificates=2*len(certificates),
        distinct_coefficient_arrays=2*len({(c['gap'], c['p']) for c in certificates}),
        exact_Pell_evaluations=sum(c['exact_Pell_evaluations'] for c in certificates),
        boundary_Horner_checks=sum(c['boundary_Horner_checks'] for c in certificates),
        scale_envelopes=envelope_audit(), residue_identities=residue_audit(),
        sole_ratio_survivor_exclusion=exceptional_summary,
        theorem='At every positive86 zero with R<0, mu<0 and X=2^p, '
                'Y<2(q^2-1)X^2, and 3p^2-19gp<12g+6 for g=2n-p. '
                'Every fixed odd gap has a finite power-branch domain; gaps1 through17 fail.',
        conclusion='The negative-input power branch has n<p<=2n-19. '
                   'Low-X data and larger gaps remain open; no universal86 theorem is claimed.')


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
    print(result['theorem'])
    print(result['conclusion'])
