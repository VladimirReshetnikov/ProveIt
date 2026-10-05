#!/usr/bin/env python3
"""Independent finite algebra for A271619; Python standard library only.

Read-only adaptation of the frozen independent checker. derive(original)
accepts the earlier interval record and returns the exact result plus vectors.
No files are opened and no output is written by this module.
Finite checks do not prove asymptotics or global localization.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt, prod
import hashlib

PN, AN, CROSS_N, ENUM_N, DEC_N = 10000, 5000, 600, 35, 28


def check(condition, message):
    """Explicit invariant guard, retained under python -O."""
    if not condition:
        raise RuntimeError(message)


def partitions(n, cap=None, length=None):
    if n == 0:
        yield ()
        return
    if length == 0:
        return
    cap = n if cap is None else min(n, cap)
    for first in range(cap, 0, -1):
        for rest in partitions(n-first, first,
                               None if length is None else length-1):
            yield (first,) + rest


def strict_partitions(n, cap=None):
    if n == 0:
        yield ()
        return
    cap = n if cap is None else min(n, cap)
    for first in range(cap, 0, -1):
        for rest in strict_partitions(n-first, first-1):
            yield (first,) + rest


def conv(a, b, n):
    z = [0]*(n+1)
    for i, ai in enumerate(a[:n+1]):
        for j, bj in enumerate(b[:n+1-i]):
            z[i+j] += ai*bj
    return z


def digest(a):
    return hashlib.sha256(('\n'.join(map(str, a))+'\n').encode()).hexdigest()


def ceildiv(a, b):
    return -((-a)//b)


def decimal_endpoint(v, scale_digits=100):
    """Exactly represent a fixed-point integer, without float conversion."""
    s = str(v).zfill(scale_digits+1)
    return s[:-scale_digits] + '.' + s[-scale_digits:]


def derive(original):
    # Ordinary partitions by unbounded coin-change DP, not pentagonal recurrence.
    p = [0]*(PN+1)
    p[0] = 1
    for part in range(1, PN+1):
        for n in range(part, PN+1):
            p[n] += p[n-part]
    # A second exact p computation via its divisor-sum differential equation.
    sigma = [0]*(CROSS_N+1)
    for d in range(1, CROSS_N+1):
        for k in range(d, CROSS_N+1, d):
            sigma[k] += d
    pp = [1]
    for n in range(1, CROSS_N+1):
        num = sum(sigma[j]*pp[n-j] for j in range(1, n+1))
        check((num % n == 0), 'Invariant failed: num % n == 0')
        pp.append(num//n)
    check((pp == p[:CROSS_N+1]), 'Invariant failed: pp == p[:CROSS_N+1]')
    check((all(sum(1 for _ in partitions(n)) == p[n]
               for n in range(ENUM_N+1))), 'Invariant failed: all(sum(1 for _ in partitions(n)) == p[n] for n in range(ENUM_N+1))')

    # Weighted strict product by descending 0/1 knapsack DP.
    a = [0]*(AN+1)
    a[0] = 1
    for k in range(1, AN+1):
        for n in range(AN, k-1, -1):
            a[n] += p[k]*a[n-k]
    # Algebraically different cross-check: A'/A logarithmic derivative.
    logarithmic = [0]*(CROSS_N+1)
    for k in range(1, CROSS_N+1):
        pk_power = 1
        for j in range(1, CROSS_N//k+1):
            pk_power *= p[k]
            logarithmic[j*k] += k*pk_power*(1 if j % 2 else -1)
    aa = [1]
    for n in range(1, CROSS_N+1):
        num = sum(logarithmic[j]*aa[n-j] for j in range(1, n+1))
        check((num % n == 0), 'Invariant failed: num % n == 0')
        aa.append(num//n)
    check((aa == a[:CROSS_N+1]), 'Invariant failed: aa == a[:CROSS_N+1]')
    check((a[0] == a[1] == 1 and all(a[n+1] > a[n] for n in range(1, AN))), 'Invariant failed: a[0] == a[1] == 1 and all(a[n+1] > a[n] for n in range(1, AN))')
    # The wrapper compares every coefficient to the frozen integer vector.
    check(digest(a) == '16dd7c5d96425fb84eb57c9840d46697c8ddd731cc4abbc0a853f2a9e1685a98',
          'Independent coefficient digest differs from the frozen baseline')

    # Direct q-bracket checks: enumerate actual diagrams, with no fitting.
    q3num, q2sqnum = [], []  # sums of 8 Q3 and 16 Q2^2
    enumeration_count = 0
    for n in range(ENUM_N+1):
        s3, s22 = 0, 0
        for lam in partitions(n):
            enumeration_count += 1
            def doubled_power(j):
                return sum((2*l-2*i+1)**j-(-2*i+1)**j
                           for i, l in enumerate(lam, 1))
            q2, q3 = doubled_power(2), doubled_power(3)
            conjugate = tuple(sum(l >= j for l in lam)
                              for j in range(1, (lam[0] if lam else 0)+1))
            for j in range(1, 7):
                conjugate_q = sum((2*l-2*i+1)**j-(-2*i+1)**j
                                  for i, l in enumerate(conjugate, 1))
                check((conjugate_q == (-1)**(j+1)*doubled_power(j)), 'Invariant failed: conjugate_q == (-1)**(j+1)*doubled_power(j)')
            s3 += q3
            s22 += q2*q2
        q3num.append(s3)
        q2sqnum.append(s22)
    eisenstein = []
    for power, factor in [(1, -24), (3, 240), (5, -504)]:
        e = [0]*(ENUM_N+1)
        e[0] = 1
        for d in range(1, ENUM_N+1):
            for n in range(d, ENUM_N+1, d):
                e[n] += factor*d**power
        eisenstein.append(e)
    e2, e4, e6 = eisenstein
    e22 = conv(e2, e2, ENUM_N)
    e222, e24 = conv(e22, e2, ENUM_N), conv(e2, e4, ENUM_N)
    numerator3 = [5*e22[n]+2*e4[n]-(7 if n == 0 else 0)
                  for n in range(ENUM_N+1)]
    numerator22 = [5*e222[n]-3*e24[n]-2*e6[n]
                   for n in range(ENUM_N+1)]
    check((conv(p, numerator3, ENUM_N) == [120*s for s in q3num]), 'Invariant failed: conv(p, numerator3, ENUM_N) == [120*s for s in q3num]')
    check((conv(p, numerator22, ENUM_N) == [405*s for s in q2sqnum]), 'Invariant failed: conv(p, numerator22, ENUM_N) == [405*s for s in q2sqnum]')

    # Exact Laurent-polynomial substitution: keys are powers of t^-1 and pi^2.
    def poly_add(*polys):
        out = {}
        for poly in polys:
            for key, v in poly.items():
                out[key] = out.get(key, F(0))+v
        return {key: v for key, v in out.items() if v}
    def poly_scale(poly, s):
        return {key: v*s for key, v in poly.items() if v*s}
    def poly_mul(p1, p2):
        out = {}
        for (a1, b1), v1 in p1.items():
            for (a2, b2), v2 in p2.items():
                key = (a1+a2, b1+b2)
                out[key] = out.get(key, F(0))+v1*v2
        return {key: v for key, v in out.items() if v}
    l2, l4, l6 = {(2,1): F(-4), (1,0): F(12)}, {(4,2): F(16)}, {(6,3): F(-64)}
    l22 = poly_mul(l2, l2)
    q3_laurent = poly_scale(poly_add(poly_scale(l22,5), poly_scale(l4,2), {(0,0): F(-7)}), F(1,960))
    q22_laurent = poly_scale(poly_add(poly_scale(poly_mul(l22,l2),5), poly_scale(poly_mul(l2,l4),-3), poly_scale(l6,-2)), F(1,6480))
    check((q3_laurent == {(4,2): F(7,60), (3,1): F(-1,2), (2,0): F(3,4), (0,0): F(-7,960)}), 'Invariant failed: q3_laurent == {(4,2): F(7,60), (3,1): F(-1,2), (2,0): F(3,4), (0,0): F(-7,960)}')
    check((q22_laurent == {(5,2): F(16,45), (4,1): F(-4,3), (3,0): F(4,3)}), 'Invariant failed: q22_laurent == {(5,2): F(16,45), (4,1): F(-4,3), (3,0): F(4,3)}')

    # Exact low-hole bijection. Generate the two sides independently, using
    # arbitrary fixed L, including L=0 and L above the natural small-n charge.
    cases, triples = 0, 0
    for n in range(DEC_N+1):
        expected = {s: prod(p[k] for k in s) for s in strict_partitions(n)}
        check((sum(expected.values()) == a[n]), 'Invariant failed: sum(expected.values()) == a[n]')
        for L in range(6):
            seen, total = {}, F(0)
            for size in range(L+1):
                for hole in combinations(range(1, L+1), size):
                    h = sum(hole)
                    ph = prod(p[k] for k in hole)
                    top = (isqrt(8*(n+h)+1)-1)//2
                    for m in range(L, top+1):
                        r = n+h-m*(m+1)//2
                        for lam in partitions(r, length=m-L):
                            fill = tuple(m-i+1+(lam[i-1] if i<=len(lam) else 0)
                                         for i in range(1, m+1))
                            outer = tuple(k for k in fill if k not in hole)
                            check((all(k in fill for k in range(1, L+1))), 'Invariant failed: all(k in fill for k in range(1, L+1))')
                            check((sum(outer) == n), 'Invariant failed: sum(outer) == n')
                            check((tuple(k for k in range(1, L+1) if k not in outer) == hole), 'Invariant failed: tuple(k for k in range(1, L+1) if k not in outer) == hole')
                            check((m == len(outer)+len(hole)), 'Invariant failed: m == len(outer)+len(hole)')
                            check((outer not in seen), 'Invariant failed: outer not in seen')
                            check((outer in expected), 'Invariant failed: outer in expected')
                            # Finite P_m B / p(H), retained as exact rational.
                            ratio = prod((F(p[fill[i-1]], p[m-i+1])
                                          for i in range(1, m+1)), start=F(1))
                            diagonal = sum(l >= i for i, l in enumerate(lam, 1))
                            frobenius_ratio = F(1)
                            for i in range(1, diagonal+1):
                                arm = lam[i-1]-i
                                leg = sum(l >= i for l in lam)-i
                                check((m-leg >= L+1), 'Invariant failed: m-leg >= L+1')
                                frobenius_ratio *= F(p[m+arm+1], p[m-leg])
                            check((ratio == frobenius_ratio), 'Invariant failed: ratio == frobenius_ratio')
                            weight = F(prod(p[1:m+1]), ph)*ratio
                            check((weight.denominator == 1), 'Invariant failed: weight.denominator == 1')
                            check((weight == expected[outer]), 'Invariant failed: weight == expected[outer]')
                            seen[outer] = (hole, m, lam)
                            total += weight
                            triples += 1
            check((set(seen) == set(expected)), 'Invariant failed: set(seen) == set(expected)')
            check((total == a[n]), 'Invariant failed: total == a[n]')
            cases += 1

    # Hole bounds, using exact integer fixed-point interval arithmetic only.
    # For g(m)=m(m+3)/2 <= k, subset partitions give p(k)>=2^m.
    N, S, digits = PN, 10**100, 100
    m0 = (isqrt(9+8*(N+1))-3)//2
    g = lambda m: m*(m+3)//2
    check((g(m0) <= N+1 < g(m0+1)), 'Invariant failed: g(m0) <= N+1 < g(m0+1)')
    for m in range(1, m0+1):
        check((p[g(m)] >= 2**m), 'Invariant failed: p[g(m)] >= 2**m')
    geometric = []
    for s in (0, 1):
        first = F(m0+2, 2**m0)*F((m0+1)*(m0+4), 2)**s
        q = F(m0+3, 2*(m0+2))*F((m0+2)*(m0+5), (m0+1)*(m0+4))**s
        check((q < 1), 'Invariant failed: q < 1')
        geometric.append(first/(1-q))
    check((geometric[0] == F(original['tail0_rational'])), "Invariant failed: geometric[0] == F(original['tail0_rational'])")
    check((geometric[1] == F(original['tail1_rational'])), "Invariant failed: geometric[1] == F(original['tail1_rational'])")
    # Tighter exact sums of full block majorants. The identities use
    # sum 2^-j=2, sum j2^-j=2, sum j^2 2^-j=6, sum j^3 2^-j=26.
    omitted = N-g(m0)+1
    tail0 = F(2*m0+6-omitted, 2**m0)
    tail1 = F(m0**3+10*m0**2+37*m0+56-omitted*g(m0+1), 2**m0)
    check((0 < tail0 <= geometric[0] < 1), 'Invariant failed: 0 < tail0 <= geometric[0] < 1')
    check((0 < tail1 <= geometric[1]), 'Invariant failed: 0 < tail1 <= geometric[1]')
    lo = {'C0': S, 'mean_hole_energy': 0, 'mean_hole_count': 0, 'variance_hole_count': 0}
    hi = dict(lo)
    for k in range(1, N+1):
        v = p[k]
        lo['C0'] = lo['C0']*(v+1)//v
        hi['C0'] = ceildiv(hi['C0']*(v+1), v)
        for key, numerator, denominator in [
                ('mean_hole_energy', k, v+1),
                ('mean_hole_count', 1, v+1),
                ('variance_hole_count', v, (v+1)**2)]:
            lo[key] += S*numerator//denominator
            hi[key] += ceildiv(S*numerator, denominator)
    # exp(tail0) <= 1/(1-tail0), so no transcendental rounding is needed.
    hi['C0'] = ceildiv(hi['C0']*tail0.denominator, tail0.denominator-tail0.numerator)
    for key in ('mean_hole_energy', 'mean_hole_count', 'variance_hole_count'):
        t = tail1 if key == 'mean_hole_energy' else tail0
        hi[key] += ceildiv(S*t.numerator, t.denominator)
    intervals = {}
    for key in lo:
        source_lo, source_hi = [F(x.strip()) for x in original['intervals'][key][1:-1].split(',')]
        check((source_lo < F(lo[key], S) < F(hi[key], S) < source_hi), 'Invariant failed: source_lo < F(lo[key], S) < F(hi[key], S) < source_hi')
        intervals[key] = [decimal_endpoint(lo[key]), decimal_endpoint(hi[key])]

    # Rational normalizations underlying the first asymptotic correction.
    # E Q3 leading: (7/60)*6^2 = 21/5.
    # E Q2^2 leading: (16/45)*6^2*sqrt(6)/pi = 64sqrt(6)/(5pi).
    check((F(7, 60)*36 == F(21, 5)), 'Invariant failed: F(7, 60)*36 == F(21, 5)')
    check((F(16, 45)*36 == F(64, 5)), 'Invariant failed: F(16, 45)*36 == F(64, 5)')
    # f'''/6 times E Q3 gives 21b/80; f''^2/8 times
    # E Q2^2 and b*sqrt(6)/pi=2 gives b/5.
    check((F(3, 8)/6*F(21, 5) == F(21, 80)), 'Invariant failed: F(3, 8)/6*F(21, 5) == F(21, 80)')
    check((F(1, 16)/8*F(64, 5)*2 == F(1, 5)), 'Invariant failed: F(1, 16)/8*F(64, 5)*2 == F(1, 5)')
    phi = F(9, 16)
    sqphi, sqphip1 = F(3, 4), F(5, 4)
    check((sqphi**2 == phi and sqphip1**2 == phi+1), 'Invariant failed: sqphi**2 == phi and sqphip1**2 == phi+1')
    check((sqphip1-sqphi == F(1, 2)), 'Invariant failed: sqphip1-sqphi == F(1, 2)')
    crossover_slope = 1/(2*sqphip1)-1/(2*sqphi)
    check((crossover_slope == -F(4, 15)), 'Invariant failed: crossover_slope == -F(4, 15)')
    check((4*phi/(phi+1) == F(36, 25)), 'Invariant failed: 4*phi/(phi+1) == F(36, 25)')
    # sqrt M: b/2+2*(-b/48-1/b); log M: -1/2+1/24-1/(2b^2).
    check((F(1, 2)-F(2, 48) == F(11, 24)), 'Invariant failed: F(1, 2)-F(2, 48) == F(11, 24)')
    check((-F(1, 2)+F(1, 24) == -F(11, 24)), 'Invariant failed: -F(1, 2)+F(1, 24) == -F(11, 24)')

    result = {
        'status': 'All exact finite checks passed; no global asymptotic claim is certified',
        'ordinary_partition_coin_change_through': PN,
        'ordinary_partition_divisor_recurrence_crosscheck_through': CROSS_N,
        'weighted_strict_coefficients_through': AN,
        'weighted_logarithmic_derivative_crosscheck_through': CROSS_N,
        'agreement_with_existing_coefficients_through': AN,
        'direct_partition_enumeration_through': ENUM_N,
        'ordinary_partitions_enumerated': enumeration_count,
        'q_brackets_checked': ['Q3', 'Q2^2'],
        'conjugation_identity_checked_for_j': list(range(1, 7)),
        'low_hole_n_range': [0, DEC_N],
        'low_hole_L_range': [0, 5],
        'low_hole_cases': cases,
        'low_hole_triples': triples,
        'frobenius_weight_identity_checked': True,
        'coefficient_sha256': digest(a),
        'partition_sha256': digest(p),
        'p_10000': str(p[10000]),
        'a_5000': str(a[5000]),
        'a_first_31': a[:31],
        'q3_sums_first_11': [str(F(v, 8)) for v in q3num[:11]],
        'q2_squared_sums_first_11': [str(F(v, 16)) for v in q2sqnum[:11]],
        'm0': m0,
        'original_tail_majorants_reproduced': [str(x) for x in geometric],
        'tighter_tail_majorants': [str(tail0), str(tail1)],
        'fixed_point_scale_digits': digits,
        'certified_intervals': intervals,
        'all_new_intervals_strictly_inside_existing_intervals': True,
        'first_edge_coefficients_over_b': ['21/80', '1/5'],
        'crossover_phi': str(phi),
        'crossover_profile_derivative': str(crossover_slope),
        'crossover_center_log_constant_without_sqrt3': '36/25',
        'logP_sqrtM_coefficients_for_b_and_inverse_b': ['11/24', '-2'],
        'logP_logM_coefficients_for_one_and_inverse_b_squared': ['-11/24', '-1/2'],
    }
    return result, a, p


if __name__ == '__main__':
    raise SystemExit('Run code/verify.py for read-only verification or code/regenerate.py for a new certificate.')
