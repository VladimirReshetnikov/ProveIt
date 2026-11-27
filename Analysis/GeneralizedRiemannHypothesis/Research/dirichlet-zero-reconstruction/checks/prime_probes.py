"""Integer-arithmetic demonstration of good probe selection for all primitive characters mod 127.

Run with Python 3. The certificate bounds the positive-frequency arithmetic leakage from |log(n/p)| <= 1
for the paper's test (u/log p) eta(u-log p) sinc(B(u-log p))^4, |eta| <= 1.
It uses no numerical ordinates or hidden asymptotic constants.
"""
from math import isqrt

X = 60000
BAND = 45000
RADIUS = 3000
UNIT = 10**14
MOD = 127
GENERATOR = 3


def primes_and_powers(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for n in range(2, isqrt(limit) + 1):
        if sieve[n]:
            sieve[n*n::n] = bytes((limit - n*n) // n + 1)
    powers = sieve.copy()
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            value = prime * prime
            while value <= limit:
                powers[value] = 1
                value *= prime
    return sieve, powers


def certified_probes():
    primes, powers = primes_and_powers(2 * X + RADIUS)
    weights = [(UNIT + d**4 - 1) // d**4 for d in range(1, RADIUS + 1)]
    good = []
    for p in range(X + 1, 2 * X):
        if not primes[p]:
            continue
        # For |m-p| <= R we have 0.95 <= m/p <= 1.05, and log(p)>10.
        # Thus sqrt(p/m)*(log(m)/log(p))^2*(max(m,p)/p)^4 < 3/2.
        # For all |log(m/p)| <= 1, this factor is < 2*exp(4) < 120.
        # These estimates use Lambda(m) <= log(m) and
        # |log(m/p)| >= |m-p|/max(m,p). Both characters have modulus <= 1.
        upper = sum(w * (powers[p-d] + powers[p+d])
                    for d, w in enumerate(weights, 1))
        # sum_{|d|>R} 1/d^4 <= 2/(3R^3); compare the combined bound to 1/8.
        # upper/UNIT bounds the local inverse fourth-power sum.
        if p**4 * (12 * upper * RADIUS**3 + 640 * UNIT) <= BAND**4 * RADIUS**3 * UNIT:
            good.append(p)
    return good, sum(primes[X+1:2*X])


def separated(k, ell):
    # |exp(2*pi*i*k*ell/126)-1| >= 1 exactly on this arc.
    phase = k * ell % (MOD - 1)
    return (MOD - 1)//6 <= phase <= 5 * (MOD - 1)//6


if __name__ == '__main__':
    good, total = certified_probes()
    logs = {pow(GENERATOR, j, MOD): j for j in range(MOD - 1)}
    assert len(logs) == MOD - 1
    shifts = list(range(1, MOD - 1))
    valid = [p for p in good if p % MOD]
    witnesses = {p: {k for k in shifts if separated(k, logs[p % MOD])} for p in valid}
    counts = [sum(k in witnesses[p] for p in valid) for k in shifts]
    left, chosen = set(shifts), []
    while left:
        p = max(valid, key=lambda r: len(witnesses[r] & left))
        if not witnesses[p] & left:
            raise ValueError('a character difference lacks a separating probe')
        chosen.append(p)
        left -= witnesses[p]
    print(f'X={X}, B={BAND}, p in ({X}, {2*X}), positive-frequency near range |log(n/p)| <= 1')
    print(f'Primes in range: {total}')
    print(f'Primes with certified near-prime-power leakage <= 1/8: {len(good)}')
    print(f'Least number of certified probes separating a fixed nontrivial character difference: {min(counts)}')
    print('Greedy common separating probes for all 125 nonprincipal characters modulo 127: ' +
          ', '.join(map(str, chosen)))
    print('Separation means complex value distance >= 1. All bounds in this example use integer arithmetic.')
