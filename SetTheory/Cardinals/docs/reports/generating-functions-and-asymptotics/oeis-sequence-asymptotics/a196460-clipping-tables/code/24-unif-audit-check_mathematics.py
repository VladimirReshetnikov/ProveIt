#!/usr/bin/env python3
"""Independent static integer/rational corroboration; no input code is loaded."""
from fractions import Fraction as Q
from math import comb, factorial, isqrt
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def alpha_integer(k):
    return sum(comb(k, r) << (r*(k-r)) for r in range(k+1))


def exp_minus_interval(x):
    """Rational enclosure using alternating Taylor on [0,1/4], then squaring."""
    assert x >= 0
    y, squares = x, 0
    while y > Q(1, 4):
        y /= 2
        squares += 1
    term = Q(1)
    partial = term
    lower = upper = None
    for i in range(1, 25):
        term *= -y/i
        partial += term
        if i == 23:
            lower = partial
        elif i == 24:
            upper = partial
    assert 0 < lower <= upper <= 1
    for _ in range(squares):
        lower *= lower
        upper *= upper
    return lower, upper


def main():
    count = dict(n_values=0, direct_normalizations=0, complement=0, raising=0,
                 squared_raising_bound=0, global_ratio=0, sharp_tail_a=0,
                 sharp_tail_c=0, leading_product_lower=0,
                 corrected_two_sided_enclosures=0, alpha_moments=0)
    rows = []
    alpha = [alpha_integer(k) for k in range(321)]
    for k, total in enumerate(alpha):
        moment4 = sum((2*r-k)**2*(comb(k,r) << (r*(k-r))) for r in range(k+1))
        assert 0 <= moment4 < 8*total
        count['alpha_moments'] += 1
    for n in range(1, 161):
        b = [comb(n, r) for r in range(n+1)]
        p = [0]*(2*n+1)
        raised = [0]*(2*n+1)
        for r in range(n+1):
            for c in range(n+1):
                weight = (b[r]*b[c]) << (r*c)
                p[r+c] += weight
                raised[r+c] += weight*((n-r)*(1 << c)+(n-c)*(1 << r))
        a = sum(b[t]*(1+(1 << t))**n for t in range(n+1))
        assert sum(p) == a
        assert sum(p[k] << (n*(2*n-k)) for k in range(2*n+1)) == a << (n*n)
        count['direct_normalizations'] += 2
        for k in range(2*n+1):
            if k <= n:
                assert p[2*n-k] == p[k] << (n*(n-k))
            else:
                assert p[k] == p[2*n-k] << (n*(k-n))
            count['complement'] += 1
            if k < 2*n:
                assert (k+1)*p[k+1] == raised[k]
                assert ((k+1)*p[k+1])**2 >= ((2*n-k)*p[k])**2 << k
                count['raising'] += 1
                count['squared_raising_bound'] += 1
                if n >= 32:
                    assert 2*(n+1)*p[k+1] <= (3*p[k]) << n
                    count['global_ratio'] += 1
        prefix = 0
        best_a = Q(0)
        best_c = Q(0)
        arg_a = []
        arg_c = []
        for ell in range(2*n):
            ha = Q(prefix, p[ell])
            hc = Q(prefix+1, p[ell]) if ell else Q(0)
            if ha > best_a:
                best_a, arg_a = ha, [ell]
            elif ha == best_a:
                arg_a.append(ell)
            if hc > best_c:
                best_c, arg_c = hc, [ell]
            elif hc == best_c:
                arg_c.append(ell)
            if n >= 32:
                wanted = Q(3*(3*n*n+n+1), n*(13*n*n-15*n+2))
                assert ha <= wanted and (ha == wanted) == (ell == 3)
                assert hc <= Q(1,n) and (hc == Q(1,n)) == (ell == 1)
                count['sharp_tail_a'] += 1
                count['sharp_tail_c'] += 1
            prefix += p[ell]
        if n >= 32:
            assert arg_a == [3] and arg_c == [1]
        if n <= 33 or n in (64, 96, 128, 160):
            rows.append(dict(n=n, a_arg_l=arg_a, a_max=str(best_a),
                             c_arg_l=arg_c, c_max=str(best_c)))
        for k in range(n+1):
            ratio = Q(p[k]*factorial(k), alpha[k]*n**k)
            assert 0 < ratio <= 1
            assert ratio >= 1-Q(k*(k-1), 2*n)
            count['leading_product_lower'] += 1
            # Test the analytic two-sided estimate nontrivially near and beyond
            # the square-root scale; all k endpoints are covered analytically.
            if n >= 3 and k >= 2 and k**3 <= 4*n*n:
                U = Q(k*(k-2), 4*n)
                eps = Q(k*(k-1)*(2*k-1), 12*n*n)*(1-Q(k-1,n))**-1
                low_u, _ = exp_minus_interval(U)
                _, high_l = exp_minus_interval(U+eps)
                assert ratio <= low_u or (U == 0 and ratio <= 1)
                assert ratio >= (1-Q(2,n))*high_l
                count['corrected_two_sided_enclosures'] += 1
        count['n_values'] += 1
    # Exact numerical constants appearing in the proof.
    assert Q(481,72) < 8 and 50 < 64
    assert Q(107,54) < 2 and Q(41,27) < 2
    assert Q(68,55)**2 < 2 and Q(33,32)**4 < 2
    assert Q(32)*Q(1,128)/(1-Q(3,66)) == Q(11,42) < Q(9,13)
    result = dict(status='PASS', counts=count, selected_maxima=rows,
                  max_n=160, exponential_enclosure_method='exact rational alternating Taylor and squaring',
                  limits='Finite corroboration only; all-n conclusions are analytic.')
    with (HERE/'evidence/mathematics.json').open('x') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    print(json.dumps(dict(status='PASS', counts=count), indent=2))


if __name__ == '__main__':
    main()
