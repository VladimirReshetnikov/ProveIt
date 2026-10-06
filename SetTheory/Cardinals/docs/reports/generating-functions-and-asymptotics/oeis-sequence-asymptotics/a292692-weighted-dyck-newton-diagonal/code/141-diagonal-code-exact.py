#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Finite exact checks for Report141; these are corroboration, not asymptotic proofs."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial

BOUND = 20
PREFIX_BOUND = 24
SOURCE_DIAGONAL = (1, 6, 217, 13997, 1283817, 151778430, 21902350480,
                   3726598826676, 729894290301789, 161683308639785288,
                   39960246577221138239)


def check(condition, name):
    if not condition:
        raise ArithmeticError(name)


def clean(p):
    p = list(map(F, p))
    while len(p) > 1 and not p[-1]: p.pop()
    return p


def add(a, b):
    c = [F(0)] * max(len(a), len(b))
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    return clean(c)


def mul(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, v in enumerate(a):
        for j, w in enumerate(b): c[i+j] += v*w
    return clean(c)


def scale(a, b): return clean([v*b for v in a])
def value(a, x): return sum(v*x**j for j, v in enumerate(a))
def encode(p): return [str(v) for v in p]


def series_mul(a, b, bound):
    c = [[F(0)] for _ in range(bound+1)]
    for i, p in enumerate(a[:bound+1]):
        for j, q in enumerate(b[:bound-i+1]): c[i+j] = add(c[i+j], mul(p, q))
    return c


def scalar_conv(a, b, bound):
    c = [F(0)] * (bound+1)
    for i, p in enumerate(a[:bound+1]):
        for j, q in enumerate(b[:bound-i+1]): c[i+j] += p*q
    return c


def direct_prefixes(bound):
    # A state remembers whether the preceding step was U. Only a newly
    # appended D after U multiplies by k + x/h. No prefix recurrence used.
    state = {(0, False): [F(1)]}
    rows = [{0: [F(1)]}]
    for x in range(bound):
        nxt = {}
        def put(key, poly): nxt[key] = add(nxt.get(key, [F(0)]), poly)
        for (height, previous_up), poly in state.items():
            put((height+1, True), poly)
            if height:
                weighted = mul(poly, [F(x, height), F(1)]) if previous_up else poly
                put((height-1, False), weighted)
        state = nxt
        by_height = {}
        for (height, previous_up), poly in state.items():
            by_height[height] = add(by_height.get(height, [F(0)]), poly)
        rows.append(by_height)
    return rows


def enumerate_paths(semilength):
    # Separate exhaustive walk construction, not state aggregation.
    out = [F(0)]
    paths = 0
    def visit(x, height, ups, previous_up, weight):
        nonlocal out, paths
        if x == 2*semilength:
            if height == 0: out = add(out, weight); paths += 1
            return
        if ups < semilength: visit(x+1, height+1, ups+1, True, weight)
        if height:
            q = mul(weight, [F(x, height), 1]) if previous_up else weight
            visit(x+1, height-1, ups, False, q)
    visit(0, 0, 0, False, [F(1)])
    return out, paths


def run():
    counts = {}
    def verify(name, condition):
        check(condition, name); counts[name] = counts.get(name, 0)+1
    p = [[F(1)]]; z = [[F(1)]]; gamma = [F(1)]
    for n in range(1, BOUND+1):
        pn = mul(p[-1], [2*n-2, 1])
        for j in range(n): pn = add(pn, mul(p[j], p[n-1-j]))
        p.append(pn)
        gamma.append(F(comb(2*n, n), 4**n))
        z.append(scale(mul(z[-1], [2*n-1, 1]), F(2*n-1, 2*n)))
        # Independent direct Pochhammer product for the hypergeometric input.
        product = [F(1)]
        for i in range(n): product = mul(product, [2*i+1, 1])
        verify('hypergeometric_product', z[n] == scale(product, gamma[n]))
        ode = add(scale(z[n-1], 2*(n-1)*(n-2)), mul(z[n-1], [4*(n-1), n-1]))
        ode = add(ode, mul(z[n-1], [F(1,2), F(1,2)]))
        verify('auxiliary_differential_equation', ode == scale(z[n], n))
        verify('ordinary_positivity', all(v >= 0 for v in pn+z[n]))
        verify('monic_polynomial', pn[-1] == 1)
        convolution = [F(0)]
        for j in range(1, n+1): convolution = add(convolution, mul(p[j], z[n-j]))
        verify('logarithmic_derivative_convolution', convolution == scale(z[n], 2*n))
        verify('coefficientwise_bound', all(a <= b for a,b in zip(pn, scale(z[n], 2*n))))
    prefixes = direct_prefixes(PREFIX_BOUND)
    prefix_records = []
    for ell in range(PREFIX_BOUND+1):
        for height in range(ell+1):
            actual = prefixes[ell].get(height, [F(0)])
            if ell >= 1:
                previous = add(prefixes[ell-1].get(height-1, [F(0)]),
                               prefixes[ell-1].get(height+1, [F(0)]))
                if ell >= 2:
                    previous = add(previous, mul(prefixes[ell-2].get(height, [F(0)]),
                                                   [F(ell-1, height+1)-1, 1]))
                verify('completed_peak_prefix_recurrence', actual == previous)
            prefix_records.append({'length':ell, 'height':height, 'polynomial':encode(actual)})
    power = [[F(1)]] + [[F(0)] for _ in range(PREFIX_BOUND//2)]
    for height in range(PREFIX_BOUND+1):
        power = series_mul(power, p, PREFIX_BOUND//2)
        for n in range((PREFIX_BOUND-height)//2+1):
            verify('weighted_prefix_power_identity', prefixes[2*n+height][height] == power[n])
    path_records = []
    for n in range(8):
        poly, paths = enumerate_paths(n)
        verify('exhaustive_paths', poly == p[n])
        verify('catalan_path_count', paths == comb(2*n,n)//(n+1))
        path_records.append({'n':n, 'paths':paths, 'polynomial':encode(poly)})
    stirling = [[0]*(BOUND+1) for _ in range(BOUND+1)]; stirling[0][0] = 1
    for n in range(1, BOUND+1):
        for m in range(1, n+1): stirling[n][m] = stirling[n-1][m-1] + m*stirling[n-1][m]
    def newton(poly, m): return sum(v*stirling[j][m] for j,v in enumerate(poly))
    def difference(poly, m, origin=0):
        return sum((-1)**(m-j)*comb(m,j)*value(poly,origin+j) for j in range(m+1))/factorial(m)
    newton_records = []
    h = [F(0)] + gamma[1:]; hpower = [F(1)] + [F(0)]*BOUND
    for m in range(BOUND+1):
        fhpower = scalar_conv(gamma, hpower, BOUND)
        for n in range(m, BOUND+1):
            pn, qn = newton(p[n],m), newton(z[n],m)
            verify('newton_p_difference', pn == difference(p[n],m))
            verify('newton_z_difference', qn == difference(z[n],m))
            odd = factorial(2*n)//(2**n*factorial(n))
            verify('newton_large_power_identity', qn == F(odd, factorial(m))*fhpower[n])
            if n: verify('newton_positive_bound', 0 <= pn <= 2*n*qn)
            newton_records.append({'N':n, 'm':m, 'P':str(pn), 'Q':str(qn), 'coefficient_fh':str(fhpower[n])})
        hpower = scalar_conv(hpower, h, BOUND)
    operator_records = []
    @lru_cache(None)
    def operator(ell, r, m):
        if r < 0 or r > ell: return F(0)
        if not ell: return F(1)
        return F(2*ell-1,2*ell)*((m+2*ell-1)*operator(ell-1,r,m)+operator(ell-1,r-1,m-1))
    for ell in range(9):
        for r in range(ell+1):
            for m in (ell,ell+3):
                coefficient = operator(ell,r,m)
                verify('newton_operator_difference', coefficient == difference(z[ell], r, m-r))
                operator_records.append({'ell':ell, 'r':r, 'm':m, 'coefficient':str(coefficient)})
        for n in range(7):
            for m in range(n+ell+1):
                lhs = newton(mul(z[ell],p[n]),m)
                rhs = sum(operator(ell,r,m)*newton(p[n],m-r) for r in range(min(ell,m)+1) if m-r<=n)
                verify('newton_operator_on_polynomial', lhs == rhs)
    diagonal = [int(newton(p[2*n],n)) for n in range(BOUND//2+1)]
    verify('public_source_diagonal', diagonal == list(SOURCE_DIAGONAL))
    return {'bounds':{'polynomial_order':BOUND,'prefix_length':PREFIX_BOUND,'exhaustive_semilength':7,'operator_order':8},
            'counts':counts,'polynomials':[{'N':n,'P':encode(p[n]),'Z':encode(z[n])} for n in range(BOUND+1)],
            'prefixes':prefix_records,'exhaustive_paths':path_records,'newton':newton_records,
            'operators':operator_records,'source_diagonal':diagonal}


if __name__ == '__main__':
    import json
    print(json.dumps(run(),sort_keys=True,indent=2,allow_nan=False))
