"""Exact finite exclusion of gap2n-p=3 for R<0 and mu>0.

The unchanged86 candidate is still unresolved.  Necessary bounds reduce
this branch to237 scale triples; integer polynomial signs and certified
ratio endpoints exclude every remaining positive scale multiplier.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

import complete75_weakened86_index_gap as parent

pell = parent.pell


def floor_root(value, degree):
    assert value >= 0 and degree >= 1
    lo, hi = 0, 1 << ((value.bit_length()+degree-1)//degree)
    assert hi**degree > value
    while hi-lo > 1:
        middle = (lo+hi)//2
        if middle**degree <= value:
            lo = middle
        else:
            hi = middle
    assert lo**degree <= value < (lo+1)**degree
    return lo


@lru_cache(None)
def shifted_psi_coefficients(base, index):
    """Exact coefficients of psi_(base+z)(index), low degree first."""
    assert base >= 1 and index >= 0
    if index == 0:
        return (0,)
    if index == 1:
        return (1,)
    previous = shifted_psi_coefficients(base, index-1)
    before = shifted_psi_coefficients(base, index-2)
    result = [0]*index
    for i, coefficient in enumerate(previous):
        result[i] += 2*base*coefficient
        result[i+1] += 2*coefficient
    for i, coefficient in enumerate(before):
        result[i] -= coefficient
    assert result[-1] == 1 << (index-1)
    return tuple(result)


def horner(coefficients, value):
    answer = 0
    for coefficient in reversed(coefficients):
        answer = answer*value+coefficient
    return answer


def finite_bounds():
    # The odd-index skipped recurrence proves that each failed inequality
    # stays failed as p increases by2, for every q>=16.
    for p in range(13, 145, 2):
        b, previous, following = (pell(2, n)[1] for n in (p, p-2, p+2))
        assert following == 14*b-previous < 14*b
    assert 16**68 >= 4*pell(2, 143)[1]
    assert 316**3 >= 4*pell(2, 13)[1]
    assert 16**67 < 4*pell(2, 141)[1]
    assert 315**3 < 4*pell(2, 13)[1]
    q_values = sorted({((1 << d)-1)*J+1
                       for d in range(4, 9)
                       for J in range(1, 314//((1 << d)-1)+1)})
    assert len(q_values) == 36 and min(q_values) == 16 and max(q_values) == 311
    triples, pair_rows = [], []
    before_main_bound = before_pairs = 0
    for q in q_values:
      for p in range(13, 142, 2):
        b = pell(2, p)[1]
        if q**((p-7)//2) >= 4*b:
            continue
        exponent = (p-3)//2
        root = floor_root(64*q**6*b**3-1, exponent)
        growth_limit = max(0, (root-1)//q**3)
        w_limit = min(growth_limit, (1 << p)//q**3)
        before_main_bound += growth_limit
        before_pairs += growth_limit > 0
        if w_limit:
            pair_rows.append(dict(q=q, p=p, growth_w_limit=growth_limit,
                                  main_root_w_limit=(1 << p)//q**3,
                                  final_w_limit=w_limit))
        for w in range(1, w_limit+1):
            X = w*q**3
            assert (X+1)**exponent < 64*q**6*b**3
            assert X <= 1 << p
            triples.append((q, p, w))
    assert before_main_bound == 930 and before_pairs == 139
    assert len(pair_rows) == 87 and len(triples) == 237
    assert sorted({q for q, _, _ in triples}) == [16, 31, 32, 46, 61, 63, 64]
    return triples, dict(p_maximum=141, q_maximum=315, q_values=q_values,
                        growth_only_qp_pairs=before_pairs,
                        growth_only_scale_triples=before_main_bound,
                        final_qp_pairs=len(pair_rows), final_scale_triples=len(triples),
                        pair_bounds=pair_rows,
                        main_root_bound='X<=2^p is retained before the ratio search.')


def ratio_polynomials(X, p):
    n = (p+3)//2
    # F(Y)=Y*k(Y)-c(Y), G(Y)=(Y+1)*k(Y)-c(Y).
    # Both are represented exactly by integer recurrence coefficients.
    F = [0]*(p+3)
    for i, coefficient in enumerate(shifted_psi_coefficients(2, p)):
        F[i] = -coefficient*(X+1)**i
    k_coefficients = [2*a*(2*X)**i
                      for i, a in enumerate(shifted_psi_coefficients(1, n))]
    for i, coefficient in enumerate(k_coefficients):
        F[2*i+1] += coefficient
    G = F.copy()
    for i, coefficient in enumerate(k_coefficients):
        G[2*i] += coefficient
    for coefficients in (F, G):
        assert all(c < 0 for c in coefficients[:p])
        assert all(c >= 0 for c in coefficients[p:])
        assert coefficients[-1] > 0
    return F, G


def ratio_values(X, Y, p):
    n = (p+3)//2
    c = pell(Y*(X+1)+2, p)[1]
    k = 2*pell(2*X*Y*Y+1, n)[1]
    return Y*k-c, (Y+1)*k-c


def certify_scale_triple(q, p, w):
    X, q3 = w*q**3, q**3
    U = (2*q*q-3)*pell(2, p)[1]+3*p-1
    limit = U//q3
    assert limit >= 1
    F, G = ratio_polynomials(X, p)
    evaluations = 0
    cache = {}
    def at(multiplier):
        nonlocal evaluations
        if multiplier not in cache:
            Y = q3*multiplier
            cache[multiplier] = ratio_values(X, Y, p)
            evaluations += 1
        return cache[multiplier]
    # F(Y)/Y^p is strictly increasing for Y>0 by the coefficient signs.
    # Find the last integer multiplier with the lower strict ratio F<0.
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
        boundary_points = (1,)
        kind = 'Lower ratio fails at the smallest positive multiplier.'
    else:
        assert 1 <= last <= limit and at(last)[0] < 0
        if last < limit:
            assert at(last+1)[0] >= 0
        # G(Y)/Y^p is also strictly increasing. Therefore G<=0 at the
        # largest remaining multiplier rules out every smaller one.
        assert at(last)[1] <= 0
        boundary_points = (last,) if last == limit else (last, last+1)
        kind = 'Upper ratio fails at the largest multiplier satisfying the lower ratio.'
    # Independent direct Pell evaluation already determined the endpoints;
    # Horner evaluation crosschecks the actual certified polynomial forms.
    for s in boundary_points:
        pair = at(s)
        assert (horner(F, q3*s), horner(G, q3*s)) == pair
    return dict(q=q, p=p, n=(p+3)//2, w=w, X=X,
                scale_multiplier_upper_bound=limit,
                last_multiplier_satisfying_lower_ratio=last,
                boundary_kind=kind, exact_recurrence_evaluations=evaluations,
                boundary_horner_crosschecks=len(boundary_points),
                ratio_solution_exists=False)


def excluded_ratio_only_fixture():
    # The larger growth-only search has a genuine ratio pair here, but
    # this does not satisfy the main root's necessary least-residue bound.
    q, p, w, s = 16, 13, 64, 131074
    X, Y = w*q**3, s*q**3
    F, G = ratio_values(X, Y, p)
    assert F < 0 < G
    assert X == 1 << 18 and X > 1 << p
    return dict(q=q, p=p, n=8, w=w, s=s, X=X, Y=Y,
                both_strict_ratios_hold=True, violates_main_root_X_bound=True,
                full_candidate_zero=False,
                scope='Ratio-only regression; explicitly excluded by the retained main-root equation.')


def verify():
    triples, bounds = finite_bounds()
    certificates = [certify_scale_triple(*t) for t in triples]
    assert len(certificates) == 237 and not any(r['ratio_solution_exists'] for r in certificates)
    return dict(status='PASS_SCOPED_WEAKENED86_GAP_THREE_EXCLUSION',
                source=parent.source_contract(), finite_bounds=bounds,
                scale_certificates=certificates,
                exact_coefficient_sign_certificates=2*len(certificates),
                exact_recurrence_evaluations=sum(r['exact_recurrence_evaluations'] for r in certificates),
                boundary_horner_crosschecks=sum(r['boundary_horner_crosschecks'] for r in certificates),
                excluded_ratio_only_regression=excluded_ratio_only_fixture(),
                conclusion='Every positive candidate zero with R<0 and mu>0 has odd p and n<p<=2n-5.',
                scope='Exact finite exclusion of the necessary gap3 domain. The86 candidate remains unresolved '
                      'for larger odd gaps and for mu<0. No finite row is claimed to be a complete candidate zero.')


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
