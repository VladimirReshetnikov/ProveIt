#!/usr/bin/env python3
"""Rigorous finite sums for the Guinand--Weil tests in the report.

Only integer and rational arithmetic is used. No third-party packages.
"""
from bisect import bisect_right
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt

UNIT = 10**15
HEIGHTS = (21, 14, 10, 6, 4, 1, -1, -4, -6, -10, -14, -21)
N = len(HEIGHTS)
NORM = sum(h*h for h in HEIGHTS)
CORR = [Q(sum(a*b for a, b in zip(HEIGHTS, HEIGHTS[j:])), NORM)
        for j in range(N+1)]


def require(test, message):
    if not test:
        raise ValueError(message)


def floor_unit(x):
    return Q((x * UNIT).__floor__(), UNIT)


def ceil_unit(x):
    return -floor_unit(-x)


def plus(x, y):
    return x[0]+y[0], x[1]+y[1]


def product(x, y):
    candidates = [a*b for a in x for b in y]
    return min(candidates), max(candidates)


def scale(a, x):
    p, q = a*x[0], a*x[1]
    return min(p, q), max(p, q)


def log_ratio(x):
    """For 1 <= x <= 2 use log x = 2 atanh((x-1)/(x+1))."""
    z = (x-1)/(x+1)
    require(0 <= z <= Q(1, 3), 'log argument')
    terms = 20
    lower = 2*sum(z**(2*j+1)/(2*j+1) for j in range(terms))
    remainder = 2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    return floor_unit(lower), ceil_unit(lower+remainder)


@lru_cache(None)
def log_int(p):
    d = p.bit_length()-1
    return plus(scale(d, log_ratio(Q(2))), log_ratio(Q(p, 2**d)))


def primes_to(limit):
    prime = bytearray([1])*(limit+1)
    prime[:2] = bytes(2)
    for p in range(2, isqrt(limit)+1):
        if prime[p]:
            prime[p*p::p] = bytes((limit-p*p)//p + 1)
    return [p for p, included in enumerate(prime) if included]


def power_weight(p, k, n, y, cut_powers, log_y, log_p):
    """Enclose 2*(-1)^k * F(k log p)/sqrt(p^k)."""
    j = bisect_right(cut_powers, n**N)-1
    if j == N:
        require(n == y, 'terminal interpolation knot')
        return Q(0), Q(0)
    coord = (N*k*log_p[0]/log_y[1]-j, N*k*log_p[1]/log_y[0]-j)
    f = plus((CORR[j], CORR[j]), scale(CORR[j+1]-CORR[j], coord))
    root_lo = isqrt(n * UNIT**2)
    reciprocal = (Q(UNIT, root_lo+1), Q(UNIT, root_lo))
    return scale(2*(-1)**k, product(f, reciprocal))


def prime_sums(y):
    log_y = log_int(y)
    knots = [y**j for j in range(N+1)]
    slope = max(abs(v-u) for u,v in zip(CORR, CORR[1:])) * N/log_y[0]
    total_lo = Q(0)
    max_ratio = Q(0)
    for p in primes_to(y):
        ratio = (Q(0), Q(0))
        n, k = p, 1
        lp = log_int(p)
        while n <= y:
            ratio = plus(ratio, power_weight(p, k, n, y, knots, log_y, lp))
            n *= p
            k += 1
        max_ratio = max(max_ratio, ceil_unit(ratio[1]))
        total_lo += floor_unit(product(ratio, lp)[0])
    return total_lo, max_ratio, slope


def main():
    # gamma > H_6 - log(7) > 1/2; log(pi) > log(31/10) > 11/10.
    require(Q(49,20)-log_int(7)[1] > Q(1,2), 'Euler gamma bound')
    require(log_int(31)[0]-log_int(10)[1] > Q(11,10), 'log pi bound')
    require(Q(11,10)+Q(1,2)+Q(1,3)+Q(1,14) > 2, 'archimedean constant')
    # EKN ceiling 2.5e25; log less than 59.
    upper_y = log_int(25*10**24)[1]
    require(upper_y < 59, 'initial EKN ceiling')
    # Rounded entries, also verified without rounding S or B internally.
    rows = [(5000, Q('62.37'), Q('.0460'), Q('60.80')),
            (4096, Q('55.94'), Q('.0488'), Q('54.50')),
            (3700, Q('52.89'), Q('.0501'), Q('51.53')),
            (3600, Q('52.10'), Q('.0506'), Q('50.74'))]
    for y, s_lower, b_upper, target in rows:
        s, b, lip = prime_sums(y)
        require(s > s_lower and b < b_upper and lip < Q(1,2), 'table')
        lower_y = (s + 2 - Q(14,9)*lip)/(1+b)
        require(lower_y > target > upper_y, 'the induction does not close')
        print(f'Y={y}: S>{s_lower}, B<{b_upper}, Lip<1/2, '
              f'forced log(D) > {target}, previous ceiling < {ceil_unit(upper_y)}')
        upper_y = log_int(4*y**6)[1]
    print(f'Exponent-six absolute discriminant ceiling: {4*rows[-1][0]**6}')
    # For exponent seven the only ramified prime in a putative omitted
    # example is |D| itself, larger than every test support.
    upper_y = log_int(39*10**29)[1]
    for y, target in [(7000,Q('76.0')), (5000,Q('63.6')), (4700,Q('61.5')), (4600,Q('60.8'))]:
        s, _, lip = prime_sums(y)
        require(s + 2 - Q(14,9)*lip > target > upper_y, 'exponent-seven induction')
        print(f'Exponent 7: Y={y}, forced log(D) > {target}')
        upper_y = log_int(4*y**7)[1]
    print(f'Exponent-seven absolute discriminant ceiling: {4*4600**7}')
    certify_split_counts()


def certify_split_counts():
    threshold = 31 * 10**19
    require(4*2000**6 < threshold, 'all small split primes excluded')
    for y, upper_disc, penalty, margin, split_count, max_b in (
            (3700, 4*3600**6, Q('.170'), Q('1.078'), 7, 5),
            (4096, 4*3600**6, Q('.192'), Q('4.20'), 22, 7),
            (5500, 25*10**24, Q('.216'), Q('5.84'), 28, 18)):
        upper_log = log_int(upper_disc)[1]
        s, b, lip = prime_sums(y)
        log_y = log_int(y)
        knots = [y**j for j in range(N+1)]
        for p in primes_to(y):
            if p <= 2000:
                continue
            require(p**2 > y, 'higher split prime power')
            inert = power_weight(p, 1, p, y, knots, log_y, log_int(p))
            loss = scale(2, product(inert, log_int(p)))[1]
            require(loss < penalty, 'per-split-prime penalty')
        certified_margin = s + 2 - Q(14,9)*lip - (1+b)*upper_log
        require(certified_margin > margin > (split_count-1)*penalty, 'split count')
        require(4*y**6 < (max_b+1)**2 * threshold, 'norm coefficient')
        print(f'Y={y}: at least {split_count} split primes above 2000; '
              f'each norm coefficient satisfies 1 <= |b| <= {max_b}.')


if __name__ == '__main__':
    main()
