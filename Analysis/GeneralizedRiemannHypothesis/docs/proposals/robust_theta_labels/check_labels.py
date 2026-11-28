#!/usr/bin/env python3
"""Exact cyclic-group regressions for the robust label criterion.
These are finite tests, not proofs of the general theorems or a Lean build.
"""
from math import gcd
from fractions import Fraction
from random import Random


def prime_factors(n):
    out = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def strip(n, p):
    while n % p == 0:
        n //= p
    return n


def orbit_length(q, r, order):
    # q is a unit modulo the order, and q^r acts trivially.
    for i in range(1, r+1):
        if pow(q, i, order) == 1 % order:
            return i
    raise AssertionError('orbit not found')


def model(q, r):
    N = q**r-1
    A = q**(r//3)
    C = (A*A+A+1)//3
    assert N == 3*C*(A-1) and gcd(C, 6*(q-1)) == 1
    return N, A, C


def witness(h, C):
    return gcd(h, 6) == 1 and h % C != 0


def power_tests(h, N, A):
    return all((h*e) % N != 0 for e in (N//2, N//3, 3*(A-1)))


def exhaustive(q, r, H):
    N, A, C = model(q, r)
    assert (q-1) % (6*H) == 0 and H % 6 == 0
    factors = prime_factors(N)
    count = 0
    nonprimitive = 0
    for h in range(N):
        ok = witness(h, C)
        assert ok == power_tests(h, N, A)
        o = N//gcd(N, h)
        # Check the exact orbit criterion, even for rejected exponents.
        robust = (orbit_length(q, r, o) == r and
                  all(orbit_length(q, r, strip(o, p)) == r for p in factors))
        assert robust == (len(prime_factors((3*C)//gcd(3*C,h))) >= 2)
        if h % 3 != 0:
            assert robust == (h % C != 0)
        if ok:
            count += 1
            nonprimitive += o != N
            # The exponent of the norm in the base-field cyclic group is h.
            norm_order = (q-1)//gcd(q-1, h)
            assert (norm_order % 6 == 0 and
                    strip(norm_order, 2) % 3 == 0 and
                    strip(norm_order, 3) % 2 == 0)
            for k in range(H):
                assert witness((h+k*(N//H)) % N, C)
            # Frobenius invariance, tested separately.
            assert witness((h*q) % N, C)
    expected = Fraction(N,3)*(1-Fraction(1,C))
    assert count == expected and count % r == 0
    assert Fraction(count, r) >= Fraction(q**r, 8*r)
    print(f'q={q}, r={r}, H={H}: N={N}, C={C}, witnesses={count}, '
          f'polynomials={count//r}, nonprimitive roots={nonprimitive}; exhaustive pass')
    return count, nonprimitive


def sampled(q, r, H, s, seed=1234):
    N, A, C = model(q, r)
    assert (q-1) % (H*H) == 0 and H % (6**s) == 0
    rng = Random(seed)
    # Do not factor N: direct exact identities for selected primes and powers.
    checks = 0
    for _ in range(2000):
        h = rng.randrange(N)
        assert power_tests(h,N,A) == witness(h,C)
        if not witness(h,C):
            continue
        checks += 1
        assert witness((h + rng.randrange(H)*(N//H)) % N,C)
        assert witness(h*q % N,C)
        o = N//gcd(N,h)
        for p in [2,3,5,7,11,13,37,101]:
            assert orbit_length(q,r,strip(o,p)) == r
            norm_order = (q-1)//gcd(q-1,h)
            assert norm_order % (6**s) == 0
            assert strip(norm_order,p) >= 2**s
    count = Fraction(N,3)*(1-Fraction(1,C))
    assert count.denominator == 1 and int(count) % r == 0
    assert count >= Fraction(q**r,8)
    print(f'q={q}, r={r}, H={H}, s={s}: {checks} accepted sampled exponents; exact density and orbit tests pass')


if __name__ == '__main__':
    a,b = exhaustive(37,3,6)
    assert b > 0
    exhaustive(73,3,6)
    # q=1297 is prime (q-1=6^4); its square level order H=36 gives s=2.
    assert prime_factors(1297) == [1297]
    sampled(1297,9,36,2)
    q,r,H=37,3,6
    N,A,C=model(q,r)
    h=7
    assert witness(h,C) and gcd(h,N)>1
    print('Strict inclusion example:', f'q={q}, r={r}, exponent={h}, order={N//gcd(N,h)} < {N}')
    print('All exact checks passed.')
