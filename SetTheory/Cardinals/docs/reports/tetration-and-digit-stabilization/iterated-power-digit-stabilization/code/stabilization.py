#!/usr/bin/env python3
"""Exact trailing-digit stabilization; Python 3.9+, standard library only.

These routines operate on valuations or modular residues. They never construct
an integer of the form a ** (B ** n). The intermediate exponent B ** n is an
ordinary integer, so arbitrary gigantic symbolic n is intentionally unsupported.
"""
from functools import lru_cache
from fractions import Fraction
from math import gcd
from typing import Dict, Tuple


def valuation(n: int, p: int) -> int:
    """p-adic valuation of a nonzero integer (caller supplies a prime p)."""
    if n == 0 or p < 2:
        raise ValueError("valuation requires n != 0 and p >= 2")
    n = abs(n)
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def decimal_profile(a: int, b: int) -> int:
    """v_10(a^(10^(b+1)) - a^(10^b)), exactly, for a >= 2 and b >= 2."""
    if a < 2 or b < 2:
        raise ValueError("require a >= 2 and b >= 2")
    if a % 10 == 0:
        return min(valuation(a, 2), valuation(a, 5)) * 10**b
    if a % 2 == 0:
        return min(valuation(a, 2) * 10**b, b + valuation(a**4 - 1, 5))
    c2 = valuation(a * a - 1, 2) - 1
    if a % 5 == 0:
        return min(valuation(a, 5) * 10**b, b + c2)
    return b + min(c2, valuation(a**4 - 1, 5))


def decimal_increment(a: int, b: int) -> int:
    if b < 3:
        raise ValueError("require b >= 3")
    return decimal_profile(a, b) - decimal_profile(a, b - 1)


def decimal_onset(a: int) -> int:
    """Least B >= 3 such that all increments at stages b >= B equal 1."""
    if a < 2 or a % 10 == 0:
        raise ValueError("require a >= 2 and 10 not dividing a")
    if gcd(a, 10) == 1:
        return 3
    if a % 2 == 0:
        t, c = valuation(a, 2), valuation(a**4 - 1, 5)
    else:
        t, c = valuation(a, 5), valuation(a*a - 1, 2) - 1
    r, power = 2, 100
    while t * power - r < c:
        r += 1
        power *= 10
    return r + 1


def minimum_failure_spec(b: int) -> Tuple[int, int, int]:
    """Return (K, j, sign): least a with D_a(b) != 1 is j*2**K + sign."""
    if b < 3:
        raise ValueError("require b >= 3")
    k = 10**(b - 1) - b + 2
    r = k % 20
    if r == 0:
        j, sign = 4, 1
    elif r == 9:
        j, sign = 3, -1
    elif r == 10:
        j, sign = 4, -1
    elif r == 19:
        j, sign = 3, 1
    else:
        j, sign = ((1, -1), (2, 1), (1, 1), (2, -1))[r % 4]
    return k, j, sign


def minimum_failure(b: int, max_bits: int = 200_000) -> int:
    k, j, sign = minimum_failure_spec(b)
    if k + j.bit_length() > max_bits:
        raise ValueError("result exceeds max_bits; use minimum_failure_spec")
    return j * 2**k + sign


def failure_density(b: int, max_power: int = 100_000) -> Fraction:
    """Natural density among ALL positive integers of admissible D_a(b) != 1."""
    if b < 3:
        raise ValueError("require b >= 3")
    r, q = b - 1, 10**(b - 1)
    if q > max_power:
        raise ValueError("density denominator exceeds requested max_power")
    return (Fraction(2 * 5**(r - 1), 2 * 5**q - 1)
            + Fraction(2**(r + 2), 5 * (5 * 2**q - 1)))


@lru_cache(maxsize=None)
def factorization(n: int) -> Tuple[Tuple[int, int], ...]:
    """Trial-division factorization; intended for small numeral radices."""
    if n < 2:
        raise ValueError("require n >= 2")
    pairs = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            e += 1
            n //= p
        if e:
            pairs.append((p, e))
        p = 3 if p == 2 else p + 2
    if n > 1:
        pairs.append((n, 1))
    return tuple(pairs)


def multiplicative_order_prime(a: int, p: int) -> int:
    if a % p == 0:
        raise ValueError("order requires a unit modulo p")
    d, x = 1, a % p
    while x != 1:
        x = x * a % p
        d += 1
    return d


def radix_profile(a: int, radix: int, n: int, lag: int = 1) -> int:
    """Exact v_radix(a^(radix^(n+lag))-a^(radix^n)); n, lag >= 1.

    Uses the local lifting formula, including every multiplicative-order
    obstruction. Factorization is by trial division, not a general fast oracle.
    """
    if a < 2 or radix < 2 or n < 1 or lag < 1:
        raise ValueError("require a, radix >= 2 and n, lag >= 1")
    local = []
    for p, e in factorization(radix):
        if a % p == 0:
            v = valuation(a, p) * radix**n
        elif p == 2:
            v = valuation(a*a - 1, 2) - 1 + n * e
        else:
            d = multiplicative_order_prime(a, p)
            if (pow(radix, n, d) * (pow(radix, lag, d) - 1)) % d:
                v = 0
            else:
                v = valuation(a**d - 1, p) + n * e
        local.append(v // e)
    return min(local)


def modular_certificate(a: int, radix: int, n: int, expected: int,
                        lag: int = 1) -> Dict[str, int]:
    """Independent modular-exponentiation witness for a predicted valuation."""
    if expected < 0:
        raise ValueError("expected valuation must be nonnegative")
    unit = radix**expected
    modulus = unit * radix
    residue = (pow(a, radix**(n + lag), modulus)
               - pow(a, radix**n, modulus)) % modulus
    assert residue % unit == 0, "predicted divisibility fails"
    digit = residue // unit
    assert 0 < digit < radix, "valuation is larger than predicted"
    return {"valuation": expected, "first_nonzero_digit": digit}


def decimal_idempotent_mod(a: int, digits: int) -> int:
    """Limit of a^(10^n) modulo 10^digits, constructed independently by CRT."""
    if a < 2 or digits < 1:
        raise ValueError("require a >= 2 and digits >= 1")
    m2, m5 = 2**digits, 5**digits
    r2, r5 = int(a % 2 != 0), int(a % 5 != 0)
    return r2 + m2 * (((r5 - r2) * pow(m2, -1, m5)) % m5)


if __name__ == "__main__":
    a = minimum_failure(3)
    print("Least counterexample:", a)
    print("Onset:", decimal_onset(a))
    for b in range(2, 7):
        s = decimal_profile(a, b)
        print("b =", b, "S =", s,
              "certificate =", modular_certificate(a, 10, b, s))
