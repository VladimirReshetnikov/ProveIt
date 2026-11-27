#!/usr/bin/env python3
"""Exact arithmetic checks for the Gaussian prime conductor paper. Python 3.9+."""
from decimal import Decimal, Inexact, localcontext, MAX_EMAX, MIN_EMIN
from math import gcd, isqrt

PRIMES = ((2, 4), (3, 3), (7, 2))
EXAMPLES = (42337, 84673)
MODULI = (8192, 2187, 343)


def divisor_sums(n, exponent, multiplier, modulus):
    a = [0] * (n + 1)
    for d in range(1, n + 1):
        term = multiplier * pow(d, exponent, modulus) % modulus
        if term:
            for j in range(d, n + 1, d):
                a[j] += term
    return [x % modulus for x in a]


def product(a, b, m):
    """Carry-free Kronecker substitution using exact decimal multiplication."""
    size = len(a)
    width = len(str(size * (m - 1) ** 2))
    def pack(v):
        return Decimal(''.join(f'{x:0{width}d}' for x in reversed(v)))
    with localcontext() as ctx:
        ctx.prec = 2 * size * width + 5
        ctx.Emax, ctx.Emin = MAX_EMAX, MIN_EMIN
        ctx.traps[Inexact] = True
        digits = format(pack(a) * pack(b), 'f')
    low = digits[-size * width:].zfill(size * width)
    return [int(low[i:i+width]) % m for i in range(len(low)-width, -1, -width)]


def quotient(n, m):
    e8 = divisor_sums(n, 7, 480, m)
    e8[0] = 1
    u = divisor_sums(n, 5, 504, m)  # 1-E6
    total = e8.copy()
    term = e8
    # Every coefficient of u is divisible by gcd(504,m).
    power = 504 % m
    while power:
        term = product(term, u, m)
        total = [(a + b) % m for a, b in zip(total, term)]
        power = power * 504 % m
    return total


def sieve(n):
    prime = bytearray(b'\x01') * (n+1)
    prime[:2] = b'\x00\x00'
    for i in range(2, isqrt(n)+1):
        if prime[i]:
            prime[i*i:n+1:i] = b'\x00' * (1+(n-i*i)//i)
    return [i for i in range(2, n+1) if prime[i]]


def valuation(n, p):
    assert n > 0
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v


def local_test(h, p, b, refined):
    v = valuation(h, p)
    double = refined and p == 2 and v == 5
    if v >= b and not (refined and (v == b or double)):
        return False
    r = 2
    # A bad interval forces p^ceil((b-1/(p-1))*r) <= h+r-1.
    # Once false, the inequality stays false.
    while True:
        num = (b*(p-1)-1)*r
        exponent = (num+p-2)//(p-1)
        if p**exponent > h+r-1:
            return True
        for start in range(max(1, h-r+1), h+1):
            if sum(valuation(x, p) for x in range(start, start+r)) >= b*r:
                return False
        r += 1


def main():
    # Exact low-order recurrence underlying the Sturm certificate.
    def sigma(k, j):
        return sum(d**j for d in range(1,k+1) if k % d == 0)
    a = [1]
    for k in range(1, 8):
        a.append(480*sigma(k,7) + 504*sum(sigma(t,5)*a[k-t] for t in range(1,k+1)))
    differences = [a[k]-984*sigma(k,1) for k in (1,3,5,7)]
    assert gcd(*differences) == 516096
    print('Sturm coefficient differences:',differences,'gcd:',gcd(*differences))
    n = max(EXAMPLES)
    for m in MODULI:
        f = quotient(n, m)
        s1 = divisor_sums(n, 1, 1, m)
        s3 = divisor_sums(n, 3, 1, m)
        prime = {8192: 2, 2187: 3, 343: 7}[m]
        for j in range(1, n+1):
            if j % prime:
                expected = {8192: 984*s1[j], 2187: (12+972*j**3)*s1[j],
                            343: 690*s1[j]+294*j*j*s3[j]}[m]
                assert f[j] == expected % m, (j,m)
        print('modulus', m, 'verified all eligible indices through', n,
              'example coefficients', [f[j] for j in EXAMPLES])
        assert all((f[j]-984*(j+1)) % m == 0 for j in EXAMPLES)
    primes = sieve(100000)
    old_fail, new_fail = [], []
    for ell in primes:
        if ell == 2:  # h(-16)=1, j nonzero
            continue
        sign = 1 if ell % 4 == 1 else -1
        h = (ell-sign)//2
        for refined, failures in [(False, old_fail), (True,new_fail)]:
            if not any(p != ell and local_test(h,p,b,refined) for p,b in PRIMES):
                failures.append(ell)
    assert old_fail == list(EXAMPLES) and not new_fail
    print('All', len(primes), 'prime conductors through 100000 verified.')
    print('Strict-test exceptions:',old_fail)
    print('Refined-test exceptions:',new_fail)
    cutoff = 456193
    extended = sieve(cutoff)
    unseen = []
    for ell in extended:
        if ell <= 100000:
            continue
        h = (ell - (1 if ell % 4 == 1 else -1)) // 2
        if not any(local_test(h,p,b,True) for p,b in reversed(PRIMES)):
            unseen.append(ell)
    assert unseen == [cutoff] and len(extended) - 1 == 38178
    print('All 38178 primes below 456193 certified. First undecided prime:',unseen[0])
    h = (cutoff-1)//2
    assert [valuation(h,p) for p in (2,3,7)] == [8,4,0] and valuation(h-1,7) == 4
    print('First undecided degree 228096. v2(h)=8, v3(h)=4, v7(h-1)=4, v7(h)=0.')


if __name__ == '__main__':
    main()
