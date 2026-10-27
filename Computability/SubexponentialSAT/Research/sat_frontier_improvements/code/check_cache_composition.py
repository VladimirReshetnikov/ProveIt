#!/usr/bin/env python3
"""Exact arithmetic checks for the eight-group time-space certificate.

These are finite consistency checks, not an asymptotic proof or SAT benchmark.
Python standard library only. Run with or without -O; all gates are explicit.
"""
import json
import math
import sys
from fractions import Fraction as F

checks = 0

def require(condition, message):
    global checks
    checks += 1
    if not condition:
        raise RuntimeError(message)


def schedule_denominator(denominator, log_lambda, low_degree=False):
    lam = 1 << log_lambda
    power = 1
    depth = 0
    while power < lam:
        power *= 3
        depth += 1
    depth += 2
    b = 6 * log_lambda
    a = 0
    prev = 0
    minimum_u = None
    margins = []
    for d in range(depth + 1):
        u = lam // (denominator * (1 << d))
        require(u >= 2, 'taper too short')
        minimum_u = u if minimum_u is None else min(minimum_u, u)
        a += u + b
        # log_2(s) >= lambda-1; M>s/lambda. Degree ceilings cost <=1 bit.
        lower_m = F(lam - 1 - log_lambda)
        if low_degree:
            row_degree = column_degree = F(lam, 7) + 1
            require(F(a + 1) < F(lam - 1, 7), 'fresh degree exceeds invariant')
        else:
            row_degree = F(9 * lam, 10) + 1
            column_degree = row_degree if d == 0 else F(prev + 1)
            require(F(a + 1) < F(9 * (lam - 1), 10), 'fresh degree exceeds invariant')
        # QR/M, Q^2*C*lambda^2/M, L*Q^2/M.
        margins.extend([
            lower_m - (3 * a + row_degree),
            lower_m - (6 * a + column_degree + 2 * log_lambda),
            lower_m - 7 * a,
        ])
        require(min(margins[-3:]) > 8 * log_lambda, 'packing margin is insufficient')
        prev = a
    return {
        'log2_lambda': log_lambda,
        'hypothetical_depth': depth,
        'minimum_u': str(minimum_u),
        'maximum_a_over_lambda': float(F(a, lam)),
        'minimum_log2_packing_margin': str(min(margins)),
    }


def main():
    r = 8
    blocks = [3, 3, 2]
    require(sum(blocks) == r, 'block partition')
    incidences = [2 * r * k - k*k - k for k in blocks]
    boundaries = [2 * k * (r-k) for k in blocks]
    crossing = [2 * blocks[i] * blocks[j] for i,j in [(0,1),(0,2),(1,2)]]
    require(incidences == [36,36,26], 'incident pair counts')
    require(boundaries == [30,30,24], 'boundary pair counts')
    require(crossing == [18,12,12], 'block pair counts')
    require(sum(crossing) + sum(k*(k-1) for k in blocks) == r*(r-1), 'all directed pairs accounted for')
    require(7**5 > 2**14, 'log_2(7)>2.8 certificate')
    require(7**100 < 2**281, 'log_2(7)<2.81 certificate')
    # gamma=sqrt(2)/4 < 5/14, a0=sqrt(14)/8 < 15/32.
    require(F(2) < F(100,49), 'sqrt2 upper bound')
    require(F(14) < F(225,16), 'sqrt14 upper bound')
    cache_ratio_upper = F(15,32) / (1-F(5,14))
    require(cache_ratio_upper == F(35,48), 'cache recurrence arithmetic')
    require(cache_ratio_upper < F(3,4), 'root dominates recursive cache accumulation')
    b_lower_sq = (30 + 12 * F(4,5)**2) / 64
    require(b_lower_sq > F(9,16), 'Strassen dominates table construction')
    ln2_partial = sum((F(2, (2*j+1) * 3**(2*j+1)) for j in range(4)), F(0))
    ln2_lower = F(6931,10000)
    require(ln2_partial > ln2_lower, 'ln2 lower bound certificate')
    pi_upper = F(22,7)
    b_upper_sq = (30 + 12 * F(81,100)**2) / 64
    high_time_sq = pi_upper**2 * 122 * b_upper_sq / ln2_lower**2
    high_space_sq = pi_upper**2 * 122 * F(30,64) / ln2_lower**2
    low_time_sq = pi_upper**2 * 30 * b_upper_sq / ln2_lower**2
    low_space_sq = pi_upper**2 * 30 * F(30,64) / ln2_lower**2
    require(high_time_sq < 39**2, 'high degree eventual time coefficient <39')
    require(high_space_sq < 35**2, 'high degree eventual space coefficient <35')
    require(low_time_sq < 20**2, 'low degree eventual time coefficient <20')
    require(low_space_sq < 18**2, 'low degree eventual space coefficient <18')
    high = [schedule_denominator(61, k) for k in [30,40,60,100,200]]
    low = [schedule_denominator(15, k, low_degree=True) for k in [30,40,60,100,200]]
    negative = []
    for den, low_flag in [(59,False),(13,True)]:
        try:
            schedule_denominator(den,60,low_degree=low_flag)
        except RuntimeError:
            negative.append({'denominator':den,'rejected':True})
        else:
            raise RuntimeError('negative schedule was not rejected')
    omega = math.log2(7)
    b_s = math.sqrt(30+12*(omega-2)**2)/8
    constants = {}
    for label,factor in [('high_degree',122),('low_degree',30)]:
        base = math.pi*math.sqrt(factor)/math.log(2)
        constants[label] = {'time':base*b_s,'space':base*math.sqrt(30)/8}
    print(json.dumps({
        'status':'pass',
        'scope':'Finite arithmetic consistency checks; no SAT benchmark or formal verification.',
        'python_optimized':bool(sys.flags.optimize),
        'explicit_checks':checks,
        'block_sizes':blocks,
        'incident_counts':incidences,
        'boundary_counts':boundaries,
        'crossing_counts':crossing,
        'recursive_cache_ratio_upper':str(cache_ratio_upper),
        'constants_float_display_only':constants,
        'high_degree_schedules':high,
        'low_degree_schedules':low,
        'negative_controls':negative,
    },indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
