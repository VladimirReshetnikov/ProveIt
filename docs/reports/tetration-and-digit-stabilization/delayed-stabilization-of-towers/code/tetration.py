"""Exact arithmetic accompanying 'Delayed stabilization of power towers'.

Python 3.10+, standard library only. No floating-point arithmetic or external
computer algebra system is needed. Tower height zero means T_0(a) = 1.
The residue iterator is deliberately guarded: reducing a tower exponent modulo
its output modulus is NOT a valid generic modular-tetration algorithm.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt


def _integer(value: int, name: str, minimum: int = 0) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def valuation(n: int, p: int) -> int:
    """Divisibility exponent of nonzero n; callers supply a prime p.

    Zero is rejected rather than confused with a finite-precision zero residue.
    For composite p this still returns the divisibility exponent, not a valuation.
    """
    _integer(p, 'p', 2)
    if not isinstance(n, int) or isinstance(n, bool) or n == 0:
        raise ValueError('valuation requires a nonzero integer')
    n = abs(n)
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def factor_trial(n: int) -> dict[int, int]:
    """Deterministic trial factorization; intended for small inputs."""
    _integer(n, 'n', 1)
    result: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def is_prime_trial(n: int) -> bool:
    """Exact primality test by all possible trial divisors up to sqrt(n)."""
    if not isinstance(n, int) or isinstance(n, bool) or n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def primes_below(limit: int) -> list[int]:
    _integer(limit, 'limit')
    sieve = bytearray(b'\x01') * limit
    if limit:
        sieve[0] = 0
    if limit > 1:
        sieve[1] = 0
    for p in range(2, isqrt(max(0, limit - 1)) + 1):
        if sieve[p]:
            sieve[p*p:limit:p] = b'\x00' * ((limit - 1 - p*p) // p + 1)
    return [p for p in range(2, limit) if sieve[p]]


def residue_towers(a: int, max_height: int, modulus: int) -> list[int]:
    """Return [T_h(a) mod modulus: 0 <= h <= max_height].

    Requires and checks a**modulus == 1 mod modulus. This suffices to make
    exponent reduction modulo modulus valid, at every iteration. Unsupported
    pairs raise ValueError instead of silently returning incorrect residues.
    """
    _integer(a, 'a', 1)
    _integer(max_height, 'max_height')
    _integer(modulus, 'modulus', 2)
    if pow(a, modulus, modulus) != 1:
        raise ValueError('unsupported pair: a**modulus is not 1 modulo modulus')
    rows = [1]
    for _ in range(max_height):
        rows.append(pow(a, rows[-1], modulus))
    return rows


def totient_25(n: int) -> int:
    """Euler phi on integers having no prime factors other than 2 and 5."""
    _integer(n, 'n', 1)
    remaining, value = n, n
    for p in (2, 5):
        if remaining % p == 0:
            value = value // p * (p - 1)
            while remaining % p == 0:
                remaining //= p
    if remaining != 1:
        raise ValueError('n has a prime factor other than 2 or 5')
    return value


def tower_mod_25_euler(a: int, height: int, modulus: int) -> int:
    """Independent Euler-chain reference for gcd(a,10)=1 and 2/5 moduli.

    Unlike residue_towers, this reduces exponents modulo phi(modulus), never
    assumes a**modulus == 1, and works for bases ending in 1, 3, 7, or 9.
    The finite-height base case takes precedence over further iteration.
    """
    _integer(a, 'a', 1)
    _integer(height, 'height')
    _integer(modulus, 'modulus', 1)
    if gcd(a, 10) != 1:
        raise ValueError('a must be coprime to 10')
    totient_25(modulus)  # validate even when height is zero
    if modulus == 1:
        return 0
    if height == 0:
        return 1
    return pow(a, tower_mod_25_euler(a, height - 1, totient_25(modulus)), modulus)


@dataclass(frozen=True)
class DecimalProfile:
    """Exact transient and permanent speed for a base a ending in 9."""
    a: int
    s: int
    t: int
    u: int
    e: int

    @classmethod
    def for_base(cls, a: int) -> 'DecimalProfile':
        _integer(a, 'a', 9)
        if a % 10 != 9:
            raise ValueError('the decimal profile requires a == 9 mod 10')
        s, t = valuation(a - 1, 2), valuation(a + 1, 2)
        return cls(a, s, t, s + t - 1, valuation(a + 1, 5))

    def stable_digits(self, h: int) -> int:
        _integer(h, 'h')
        return min(self.s + h*self.u, h*self.e)

    def speed(self, h: int) -> int:
        _integer(h, 'h', 1)
        return self.stable_digits(h) - self.stable_digits(h - 1)

    @property
    def eventual_speed(self) -> int:
        return min(self.u, self.e)

    @property
    def onset(self) -> int:
        if self.e <= self.u:
            return 1
        delta = self.e - self.u
        return 1 + (self.s + delta - 1) // delta


def prime_delay_progression(s: int) -> tuple[int, int]:
    """CRT class (r, M) with v2(a-1)=s, v5(a+1)=s+1 and onset s+1.

    Every positive a == r mod M has the specified valuations. Dirichlet's
    theorem proves that the class contains infinitely many primes.
    """
    _integer(s, 's', 2)
    m2, m5 = 2**(s+1), 5**(s+2)
    r2, r5 = 1 + 2**s, 5**(s+1) - 1
    modulus = m2 * m5
    residue = (r2 + m2 * (((r5 - r2)*pow(m2, -1, m5)) % m5)) % modulus
    if gcd(residue, modulus) != 1:
        raise ArithmeticError('CRT class was not reduced')
    return residue, modulus


def delay_tail_density(k: int) -> Fraction:
    """Relative natural density of onset > k among integers ending in 9."""
    _integer(k, 'k', 2)
    return Fraction(4, 9*(5*10**(k-1) - 1))


def stable_radix_residue(B: int, digits: int) -> int:
    """Unique fixed residue modulo B**digits for towers of base B-1.

    Increasing-precision digit lifting; no factorization is needed.
    """
    _integer(B, 'B', 4)
    _integer(digits, 'digits', 1)
    if B % 2:
        raise ValueError('B must be even')
    a, x, modulus = B - 1, B - 1, B
    for _ in range(1, digits):
        modulus *= B
        x = pow(a, x, modulus)
    return x


def local_lines(a: int, radix: int) -> dict[int, tuple[int, int, int]]:
    """Return prime -> (intercept, slope, radix exponent).

    Requires odd a >= 3 and every prime divisor of radix to divide a*a-1.
    A deliberately small-input trial factorization is used for radix.
    """
    _integer(a, 'a', 3)
    _integer(radix, 'radix', 2)
    if a % 2 == 0:
        raise ValueError('a must be odd')
    result = {}
    for p, power in factor_trial(radix).items():
        if p == 2:
            s, t = valuation(a-1, 2), valuation(a+1, 2)
            result[p] = (s, s+t-1, power)
        elif (a-1) % p == 0:
            r = valuation(a-1, p)
            result[p] = (r, r, power)
        elif (a+1) % p == 0:
            result[p] = (0, valuation(a+1, p), power)
        else:
            raise ValueError('every prime divisor of radix must divide a*a-1')
    return result


def stable_digits_radix(a: int, radix: int, height: int) -> int:
    _integer(height, 'height')
    return min((alpha + height*beta) // power
               for alpha, beta, power in local_lines(a, radix).values())


def first_permanent_height(a: int, radix: int, digits: int) -> int:
    _integer(digits, 'digits', 1)
    return max(max(0, (digits*power-alpha+beta-1)//beta)
               for alpha, beta, power in local_lines(a, radix).values())
