#!/usr/bin/env python3
"""Check finite prime-jump witnesses for the residue reconstruction theorem."""
from math import gcd, isqrt


def is_prime(n):
    if n < 2:
        return False
    return all(n % factor for factor in range(2, isqrt(n) + 1))


def legendre(n, d):
    residue = pow(n, (d - 1) // 2, d)
    return -1 if residue == d - 1 else residue


def check_witnesses(q, d, expected):
    assert is_prime(d) and d % 8 == 7 and q % 8 == 0 and gcd(q, d) == 1
    common = 0
    found = []
    for k in range(1, (expected[-1] - 1) // q + 1):
        p = 1 + k * q
        if is_prime(p) and legendre(p, d) == -1:
            common = gcd(common, p - 1)
            found.append(p)
            print(f'q={q}, d={d}, p={p}, (p-1)/q={k}, cumulative gcd={common}')
    assert found == expected
    assert common == q


if __name__ == '__main__':
    check_witnesses(8, 7, [17, 41])
    q, d = 18480, 9239
    assert d % q == q // 2 - 1
    assert all(legendre(p, d) == 1
               for p in range(2, q + 1) if q % p == 0 and is_prime(p))
    check_witnesses(q, d, [258721, 794641])
