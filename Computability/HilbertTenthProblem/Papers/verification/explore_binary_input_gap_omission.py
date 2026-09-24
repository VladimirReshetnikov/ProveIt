#!/usr/bin/env python3
"""Scoped refutation: delete only the input-gap addition from published 90.

The companion proof supplies a fixed singleton compiler index and a full
positive Pell extension.  Finite arithmetic cases below do not pretend to
materialize that enormous compiler index or its Pell coordinates.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path

import sympy as sp

import round37_1980_binary_product_certificate as old


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def verify_source():
    schedule = [row for row in old.SCHEDULE if row[0] != 'bx']
    need([row for row in old.SCHEDULE if row[0] == 'bx'] ==
         [('bx', '+', 'x', 'beta')], 'exact one-addition deletion')
    need(old.EQUALITIES[1] == ('b', 'bx'), 'exact deleted input-gap equality')
    equalities = [(i, pair) for i, pair in enumerate(old.EQUALITIES) if i != 1]
    names = [name for name in old.NAMES if name != 'beta']
    used = {a for _, _, l, r in schedule for a in (l, r) if isinstance(a, str)}
    used |= {a for _, pair in equalities for a in pair}
    need('bx' not in used and 'beta' not in used, 'no dangling register or unknown')
    need(set(names) <= used, 'every retained positive coordinate participates')
    env = {name: old.SYM[name] for name in names}
    histogram = old.baseline.run_schedule(schedule, env)
    counts = Counter(op for _, op, _, _ in schedule)
    need(len(schedule) == 89 and counts['*'] == 48 and
         counts['+'] + counts['-'] == 41, '89 = 48M + 41A')
    need(len(names)-len(old.PARAMETERS) == 33 and len(equalities) == 21,
         '33 positive unknowns and 21 equations')
    source, s = old.source_residuals(), old.SYM
    A, B = s['a']+2, s['H']+s['b']+2
    aux_u = 2*s['r']+1+s['j']*s['c']
    corrections = {
        2: -s['la']*source[3],
        16: source[15]*(aux_u**2-s['y_aux']**2),
        17: source[3]*(s['ka']+s['rho']*(source[3]-2*(A-B))),
    }
    records = []
    for index, (left, right) in equalities:
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual-source[index]-correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual+source[index]) == 0:
            sign = -1
        else:
            raise AssertionError('source mismatch: '+str(index))
        need(s['beta'] not in source[index].free_symbols, 'deleted coordinate absent')
        records.append(dict(published_index=index, equality=[left, right],
                            sign=sign, correction=sp.sstr(sp.expand(correction))))
    # The positive prerequisites of every nonzero correction are retained.
    need(all(i in [j for j, _ in equalities] for i in (3, 15)),
         'unchanged acyclic source correction prerequisites')
    return dict(operations=89, multiplications=48, additions=41,
                positive_unknowns=33, equations=21, histogram=histogram,
                removed_instruction=['bx', '+', 'x', 'beta'],
                source_checks=records)


def shift_case(L, v, s, extra_width):
    """Real exact coding/mask values, deliberately not an actual compiler code."""
    need(0 < v < s and 3*s+3 < L, 'small finite support range')
    w = s+1
    H0 = 1 << (2*L+8)
    B = H0 << extra_width
    b, theta = B-H0-1, B-2
    x0, g0 = 2, B**v+B**s
    ell = B**v+B**s
    e = ell+B**w
    C = x0+g0
    q = B**L
    n = q**8
    sigma = (e-ell)*C*C
    alpha = q-ell-sigma
    V = 2**v+2**s+2**L*(2**v+2**s+2**w)
    lam = (q*q-1)//(B-1)
    t = (ell+e*q-V)//theta
    need(all(a > 0 for a in (b, theta, g0, ell, e, sigma, alpha, lam, t)),
         'positive finite coding witnesses')
    need(b > x0 and H0 > 3*L and B >= 2*H0,
         'old input gap and numerical radix thresholds')
    need(q*q-1 == lam*(B-1) and ell+e*q == V+t*theta,
         'geometry and fixed congruence')
    S2 = ell+e*q
    Tplus = q*q*(1+theta*lam)+ell*(theta*q**4-b)
    T1, T2, T3 = q*q-1-b*ell, theta*lam, theta*ell
    need(Tplus-1 == T1+q*q*T2+q**4*T3, 'exact packed mask blocks')
    need(0 <= T1 < q*q and 0 <= T2 < q*q and 0 <= T3 < q**4,
         'mask block widths')
    shifted = []
    for removed in (B**v, B**s):
        x, g = x0+removed, g0-removed
        need(x > b and g > 0 and x+g == C, 'false larger input, positive remaining g')
        need((g0 & removed) == removed and g == (g0 ^ removed),
             'subtraction only clears an existing allowed bit')
        need((g0 & T1) == (g & T1) == (S2 & T2) == (sigma & T3) == 0,
             'all original and transported masks pass')
        oldS = g0+q*q*(S2+q*q*sigma)
        S = g+q*q*(S2+q*q*sigma)
        oldr = oldS*(n*n-n)+Tplus*(n*n-1)
        r = S*(n*n-n)+Tplus*(n*n-1)
        need(oldr-r == removed*(n*n-n), 'exact changed index')
        need(0 < S < oldS < n and 0 < Tplus < n,
             'unchanged strict packing range')
        need(n*n-1 <= r < 2*n**3 and r % 2 == 0,
             'retained Pell prebounds and even index')
        need(S & (Tplus-1) == 0, 'full mask')
        required = 2*(n.bit_length()-1)
        need(r.bit_count() >= required, 'actual central-binomial valuation')
        need(2*(n.bit_length()-1) < 2*r+1,
             'canonical power-of-two U is divisible by n squared')
        need(L >= 2 and 3*L <= B and L < 2*r+1,
             'canonical second-index hypotheses')
        need(ell+sigma+alpha == q and sigma == (e-ell)*(x+g)**2,
             'all retained nonlinear coding equations')
        shifted.append(dict(removed_position=v if removed == B**v else s,
                            queried_input_bits=x.bit_length(),
                            packed_index_bits=r.bit_length(),
                            valuation=r.bit_count(), required_valuation=required))
    return dict(L=L, positions=[v, s], radix_bits=B.bit_length(),
                fixed_congruence_bits=V.bit_length(), cases=shifted)


def verify():
    source = verify_source()
    cases = [shift_case(L, v, s, width)
             for L in (16, 32, 64)
             for v, s in ((1, 2), (1, 3), (2, 3))
             for width in (1, 2)]
    return dict(status='PASS', classification='Refutation of the input-gap deletion only',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS without findings.',
                source=source, arithmetic_families=cases,
                transported_masks=sum(len(case['cases']) for case in cases),
                scope=('All 21 residuals and the exact 89-operation schedule are checked. '
                       'The 36 transported complete-mask cases use small illustrative code '
                       'polynomials, not universal compiler indices. The companion note proves '
                       'the same transformation at one fixed genuine singleton compiler index '
                       'and constructs all positive Pell witnesses by the published general '
                       'converse. Enormous complete Pell coordinates are not materialized.'))


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n',
                                                encoding='utf-8')
    print(result['status'], result['source']['operations'],
          result['transported_masks'], 'transported complete masks')
