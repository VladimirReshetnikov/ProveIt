"""Effective fixed-gap reduction and exact gap11 exclusion for complete86.

All deductions retain the unchanged complete compiler, full strong norm,
both ratios and positive input root. Finite necessary-domain certificates
are not complete candidate zeros. Larger gaps and mu<0 remain open.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path
import random

import complete75_weakened86_gap_nine as previous

helpers = previous.helpers
pell = previous.pell
GAP = 11
source_contract = previous.source_contract


def lane_bounds(gap, d, J, w):
    """A proved uniform tail cutoff in one arbitrary fixed-gap low-X lane."""
    assert gap >= 3 and gap % 2 == 1 and d >= 4 and J >= 1 and w >= 1
    B = 1 << d
    q = (B-1)*J+1
    X = w*q**3
    assert X+1 < 1 << (2*gap)
    M = q*q-1
    umin, umax = 2*d+1, 2*d*((q-2)//(2*d))+B-1
    h = (X+1).bit_length()-1
    assert h >= 12 and 1 << h <= X+1
    T = q**4+M*(1 << umax)+2
    A0, A1 = 3*X*T+2*(2*q*q-3)*(X*X-1), 3*X
    # Two-index doubling is sufficient when h>=gap. Otherwise use all
    # gap odd residue classes modulo2gap, with exact exponent increment h.
    step = 2 if h >= gap else 2*gap
    increment = 1 if h >= gap else h
    cutoff = max(13, gap+2)
    while True:
        exponent = (h*(cutoff-gap)-2*(gap+1))//(2*gap)
        window_end = cutoff+step-2
        if exponent >= 0 and 1 << exponent > max(
                A0+A1*window_end, window_end, umax):
            break
        cutoff += 2
    factor = 1 << increment
    assert factor*(A0+A1*cutoff) > A0+A1*(cutoff+step)
    assert factor*cutoff > cutoff+step
    assert X > 2*(2*q*q-3)
    return dict(gap=gap, d=d, B=B, J=J, q=q, w=w, X=X,
        valuation_X=(X & -X).bit_length()-1,
        floor_log2_X_plus_one=h, input_index_minimum=umin,
        input_index_maximum=umax, theta_upper_bound=T,
        residue_constant_bound=A0, residue_linear_bound=A1,
        large_index_cutoff=cutoff, cutoff_exponent=exponent,
        induction_step=step, exponent_increment_lower_bound=increment)


def necessary_indices(lane):
    gap, X, q = lane['gap'], lane['X'], lane['q']
    ell = lane['valuation_X']
    result = []
    for p in range(max(13, gap+2), lane['large_index_cutoff'], 2):
        if X >= 1 << p:
            continue
        # H is odd; H divides the quotient after removing v2(X).
        assert ((1 << p)-X) % (1 << ell) == 0
        N = ((1 << p)-X) >> ell
        if N < 4*q**3*(X+1)+3:
            continue
        exponent = gap*(p-ell)-gap+1
        if exponent <= 0 or (X+1)**((p+gap)//2) >= 1 << exponent:
            continue
        result.append(p)
    return result


def finite_domains(gap=GAP):
    assert gap >= 3 and gap % 2 == 1
    cap = (1 << (2*gap))-2
    lanes = []
    d = 4
    while (1 << d)**3 <= cap:
        B, J = 1 << d, 1
        while ((B-1)*J+1)**3 <= cap:
            q = (B-1)*J+1
            for w in range(1, cap//q**3+1):
                lane = lane_bounds(gap, d, J, w)
                lane['remaining_odd_indices'] = necessary_indices(lane)
                lanes.append(lane)
            J += 1
        d += 1
    power = [(1 << t, p, 1 << (p-3*t))
             for p in range(max(13, gap+2), (19*gap-1)//3+1, 2)
             for t in range(4, p//3+1)]
    low = sorted({(r['q'], p, r['w']) for r in lanes
                  for p in r['remaining_odd_indices']})
    assert all(3*p < 19*gap and w*q**3 == 1 << p for q, p, w in power)
    if gap == GAP:
        assert len(lanes) == 1414 and len(power) == 300 and len(low) == 1113
        assert min(r['large_index_cutoff'] for r in lanes) == 69
        assert max(r['large_index_cutoff'] for r in lanes) == 317
    return lanes, power, low


@lru_cache(None)
def ratio_polynomials(X, p):
    n = (p+GAP)//2
    F = [0]*(p+GAP)
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
    n = (p+GAP)//2
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
    if at(1)[0] >= 0:
        last = 0
    else:
        # Start at the smallest permitted scale; geometric bracketing
        # avoids expensive evaluations far above the unique sign boundary.
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
    points = {1} if last == 0 else {last}
    if last == 0:
        kind = 'Lower ratio fails at the smallest scale.'
    else:
        assert at(last)[0] < 0
        if last < limit:
            assert at(last+1)[0] >= 0
            points.add(last+1)
        assert at(last)[1] <= 0, ('Ratio survivor', q, p, w, last)
        kind = 'Upper ratio fails at the last lower-ratio scale.'
    for s in points:
        assert (helpers.horner(F, q3*s), helpers.horner(G, q3*s)) == at(s)
    return dict(q=q, p=p, n=(p+GAP)//2, w=w, X=X,
        scale_multiplier_upper_bound=limit,
        last_multiplier_satisfying_lower_ratio=last, boundary_kind=kind,
        exact_recurrence_evaluations=len(cache), boundary_horner_crosschecks=len(points))


def general_cutoff_audit(lanes):
    # The fixed-gap theorem does not require h>=gap or2^umin>q.
    extras = [lane_bounds(g, 4, J, w) for g, J, w in
        ((13, 1, 1), (21, 273, 1), (51, 1, 1), (101, 273, 3))]
    cases = 0
    for lane in lanes+extras:
        gap, h = lane['gap'], lane['floor_log2_X_plus_one']
        start, step = lane['large_index_cutoff'], lane['induction_step']
        A0, A1 = lane['residue_constant_bound'], lane['residue_linear_bound']
        def exp(p): return (h*(p-gap)-2*(gap+1))//(2*gap)
        for offset in range(0, step, 2):
            for repeat in (0, 1, 2, 17):
                p = start+offset+step*repeat
                assert 1 << exp(p) > max(A0+A1*p, p, lane['input_index_maximum'])
                assert exp(p+step) >= exp(p)+lane['exponent_increment_lower_bound']
                factor = 1 << lane['exponent_increment_lower_bound']
                assert factor*(A0+A1*p) > A0+A1*(p+step)
                assert factor*p > p+step
                cases += 1
    assert any(r['floor_log2_X_plus_one'] < r['gap'] for r in extras)
    assert any((1 << r['input_index_minimum']) <= r['q'] for r in extras)
    return dict(exact_induction_envelope_cases=cases, additional_general_gap_lanes=extras,
        scope='Finite checks supplement the arbitrary-fixed-gap induction proof.')


def packing_positivity_audit():
    rng = random.Random(86111414)
    count = beyond_old_lower_bound = 0
    for d in range(4, 9):
      for J in (1, 2, 17, 273):
       B, q = 1 << d, ((1 << d)-1)*J+1
       M = q*q-1
       for _ in range(24):
        x = rng.randrange(1, (q-2)//(2*d)+1)
        available = q-2*d*x
        F = rng.randrange(1, available)
        alpha = rng.randrange(1, available-F+1)
        C = q-F-alpha-2*d*x
        MC, MF = rng.randrange(1, B), rng.randrange(1, B)
        packed = (MC+q*(MF+B-1))*J
        K = q*(q-F)*M+packed
        assert K-M*C == M*((q-1)*C+q*(alpha+2*d*x))+packed > 0
        for u in (2*d+1, 2*d*x+1):
            for epsilon, lam in ((-1, 1), (1, -1)):
                assert K-M*C+M*(1 << u)+epsilon-lam > 0
                count += 1
        beyond_old_lower_bound += (1 << (2*d+1)) <= q
    return dict(positive_packing_identity_cases=count,
        packing_tuples_beyond_old_input_lower_bound=beyond_old_lower_bound,
        scope='Packing identities only; masks are positive test coefficients, not asserted full compiler witnesses.')


def verify():
    lanes, power, low = finite_domains()
    certificates = [certify_scale_triple(*t) for t in power+low]
    assert len(certificates) == 1413
    return dict(status='PASS_SCOPED_WEAKENED86_GAP_ELEVEN_EXCLUSION',
        source=source_contract(), gap=GAP, low_X_lanes=lanes,
        finite_power_branch_triples=len(power), finite_low_branch_triples=len(low),
        scale_certificates=certificates,
        per_triple_coefficient_sign_certificates=2*len(certificates),
        distinct_coefficient_arrays=2*len({(c['X'], c['p']) for c in certificates}),
        exact_recurrence_evaluations=sum(c['exact_recurrence_evaluations'] for c in certificates),
        boundary_horner_crosschecks=sum(c['boundary_horner_crosschecks'] for c in certificates),
        general_cutoff_audit=general_cutoff_audit(lanes),
        packing_positivity_audit=packing_positivity_audit(),
        retained_input_classification=previous.input_index_audit(),
        main_wrap_corrections=previous.residue_audit(),
        conclusion='Every positive candidate zero with R<0 and mu>0 has odd p and n<p<=2n-13.',
        scope='Gap11 is excluded under the unchanged complete86 compiler contract. Every fixed odd '
              'gap admits the stated effective finite necessary-domain reduction; no uniform gap bound '
              'or universal86 theorem follows. Gaps>=13 and mu<0 remain unresolved.')


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
