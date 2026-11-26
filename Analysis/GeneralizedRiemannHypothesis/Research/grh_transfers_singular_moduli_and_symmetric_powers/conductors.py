"""Independently check the valuation cut, at every prime conductor up to 100,000."""
from math import isqrt


def primes_through(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p::p] = bytes(1 + (limit - p * p) // p)
    return [p for p, flag in enumerate(flags) if flag]


def cuts_through(p, slope, h_max):
    # w(n) >= n * (slope - 1/(p-1)); the omitted suffix exceeds slope*h_max.
    end = slope * h_max * (p - 1) // (slope * (p - 1) - 1) + 1
    weights = [0]
    for n in range(1, end + 1):
        m = n
        v = 0
        while m % p == 0:
            m //= p
            v += 1
        weights.append(weights[-1] + slope - v)
    suffix_min = weights.copy()
    for n in range(end - 1, -1, -1):
        suffix_min[n] = min(weights[n], suffix_min[n+1])
    prefix_max = 0
    good = [False]
    for h in range(1, h_max + 1):
        good.append(prefix_max < suffix_min[h])
        prefix_max = max(prefix_max, weights[h])
    return good


if __name__ == '__main__':
    limit = 100_000
    ell_list = [p for p in primes_through(limit) if p not in (2, 3, 7)]
    h_max = (limit + 1) // 2
    at_two = cuts_through(2, 4, h_max)
    at_three = cuts_through(3, 3, h_max)
    at_seven = cuts_through(7, 2, h_max)
    counts = {}
    first = {}
    for ell in ell_list:
        sign = 1 if ell % 4 == 1 else -1
        h = (ell-sign)//2
        case = at_two[h], at_three[h], at_seven[h]
        counts[case] = counts.get(case, 0) + 1
        first.setdefault(case, (ell, h))
    print('prime conductors <=', limit, 'excluding 2, 3 and 7:', len(ell_list))
    for case in sorted(counts):
        print('pass at (2, 3, 7):', case, 'count:', counts[case], 'first (ell,h):', first[case])
    for ell in (197, 15877):
        h = (ell - (1 if ell%4 == 1 else -1))//2
        print('ell:', ell, 'h:', h, 'passes:', at_two[h], at_three[h], at_seven[h])
