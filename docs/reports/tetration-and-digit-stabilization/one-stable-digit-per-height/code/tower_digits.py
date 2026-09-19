#!/usr/bin/env python3
"""Exact residues of (q-1)-based towers, for even q >= 4.

Only Python's standard library is needed.  Heights and Knuth arrow ranks may
be enormous integers.  Arithmetic cost is controlled by the output precision.
See article.tex for proofs, including the restricted-domain exponent reduction.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from fractions import Fraction
from math import factorial


def _integer(name: str, value: int, minimum: int) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def _parameters(q: int, precision: int) -> None:
    _integer("q", q, 4)
    _integer("precision", precision, 1)
    if q % 2:
        raise ValueError("q must be even (the base of the tower is q - 1)")


def valuation(n: int, p: int) -> int:
    """The p-adic valuation of a nonzero integer, with p assumed prime."""
    _integer("p", p, 2)
    if n == 0:
        raise ValueError("valuation(0) is infinite, not an integer")
    n = abs(n)
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def factor(n: int) -> dict[int, int]:
    """Trial factorization, intended for small q and the independent test oracle."""
    _integer("n", n, 1)
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


@lru_cache(maxsize=4096, typed=True)
def stable_residue(q: int, precision: int) -> int:
    """Unique x modulo q**precision satisfying (q-1)**x == x.

    Digit lifting uses moduli q, q**2, ..., q**precision.  No factoring.
    """
    _parameters(q, precision)
    a, modulus, x = q - 1, q, q - 1
    for _ in range(2, precision + 1):
        modulus *= q
        x = pow(a, x, modulus)
    return x


def tetration_mod(q: int, height: int, precision: int) -> int:
    """(q-1) ↑↑ height mod q**precision, with height zero interpreted as 1."""
    _parameters(q, precision)
    _integer("height", height, 0)
    if height >= precision:
        return stable_residue(q, precision)
    modulus, a, x = q**precision, q - 1, 1
    for _ in range(height):
        x = pow(a, x, modulus)
    return x


def difference_residue(q: int, height: int, gap: int, extra: int = 1) -> int:
    """(T[height+gap]-T[height])/q**height modulo q**extra."""
    _parameters(q, extra)
    _integer("height", height, 0)
    _integer("gap", gap, 1)
    modulus = q ** (height + extra)
    delta = (tetration_mod(q, height + gap, height + extra)
             - tetration_mod(q, height, height + extra)) % modulus
    assert delta % q**height == 0
    return delta // q**height


def predicted_prime_distance(q: int, height: int, p: int) -> int:
    """v_p(T[height+gap]-T[height]), independent of every positive gap."""
    _parameters(q, 1)
    _integer("height", height, 0)
    primes = factor(q)
    if p not in primes:
        raise ValueError("p must be a prime divisor of q")
    if p != 2:
        return height * primes[p]
    u, v = valuation(q - 2, 2), primes[2]
    return u + height * (u + v - 1)


def _ceil_log(a: int, cap: int) -> int:
    """Smallest e >= 0 with a**e >= cap, using bounded exact integers."""
    e, x = 0, 1
    while x < cap:
        e += 1
        x *= a
    return e


@lru_cache(maxsize=16384, typed=True)
def capped_hyper(a: int, rank: int, n: int, cap: int) -> int:
    """min(a ↑^rank n, cap), for a >= 3, rank >= 1, n >= 0, cap >= 1.

    H_rank(n) >= a**n; for rank >= 2 and n >= 2, H_rank(n) >= a**rank.
    These guards prevent recursion through enormous ranks or arguments.
    """
    _integer("a", a, 3)
    _integer("rank", rank, 1)
    _integer("n", n, 0)
    _integer("cap", cap, 1)
    if cap == 1:
        return 1
    if n == 0:
        return 1
    if n == 1:
        return min(a, cap)
    threshold = _ceil_log(a, cap)
    if n >= threshold or (rank >= 2 and rank >= threshold):
        return cap
    if rank == 1:
        return a**n  # n < threshold, so the result is strictly below cap.
    x = 1
    for _ in range(n):
        x = capped_hyper(a, rank - 1, x, cap)
        if x == cap:
            break
    return x


def knuth_mod(q: int, rank: int, n: int, precision: int) -> int:
    """(q-1) ↑^rank n mod q**precision; rank 1 is ordinary exponentiation."""
    _parameters(q, precision)
    _integer("rank", rank, 1)
    _integer("n", n, 0)
    a, modulus = q - 1, q**precision
    while True:
        if n == 0:
            return 1
        if n == 1:
            return a
        if rank == 1:
            return pow(a, n, modulus)
        if rank == 2:
            return tetration_mod(q, n, precision)
        # Tower-height bound J_rank(n) >= n + rank - 2.
        if n + rank - 2 >= precision:
            return stable_residue(q, precision)
        inner = capped_hyper(a, rank, n - 1, precision)
        if inner == precision:
            return stable_residue(q, precision)
        n, rank = inner, rank - 1


def local_lambert_residue(q: int, p: int, precision: int) -> int:
    """Independent rational-series evaluation of the local fixed point mod p**K.

    This is an educational check, not the efficient production evaluator.
    It evaluates truncated p-adic log and Lambert series using exact Fraction.
    Sign information at p=2 is retained explicitly.  Measured precision is in
    p-adic digits here, not q-adic digits.
    """
    _parameters(q, 1)
    _integer("precision", precision, 1)
    if p not in factor(q):
        raise ValueError("p must be a prime divisor of q")
    epsilon = 1 if p == 2 and q % 4 == 2 else -1
    b = epsilon * (q - 1)  # a = epsilon*b; b is a principal unit.
    t = b - 1
    work = precision + 4
    terms = 2 * work + 4
    ell = sum((Fraction((-1) ** (j + 1) * t**j, j)
               for j in range(1, terms + 1)), Fraction(0))
    total, ell_power = Fraction(0), Fraction(1)
    for n in range(1, terms + 1):
        coefficient = Fraction(-((-n) ** (n - 1)) * ((-epsilon) ** n), factorial(n))
        total += coefficient * ell_power
        ell_power *= ell
    modulus = p**precision
    assert total.denominator % p != 0
    return (total.numerator * pow(total.denominator, -1, modulus)) % modulus


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("q", type=int, help="even radix >= 4; tower base is q-1")
    parser.add_argument("precision", type=int, help="number of radix-q digits")
    parser.add_argument("--height", type=int, help="finite tetration height (default: stable limit)")
    parser.add_argument("--rank", type=int, help="number of Knuth arrows; requires --argument")
    parser.add_argument("--argument", type=int, help="right argument of a Knuth operation")
    args = parser.parse_args()
    try:
        if args.rank is not None:
            if args.argument is None or args.height is not None:
                parser.error("--rank requires --argument and excludes --height")
            result = knuth_mod(args.q, args.rank, args.argument, args.precision)
        elif args.argument is not None:
            parser.error("--argument requires --rank")
        elif args.height is not None:
            result = tetration_mod(args.q, args.height, args.precision)
        else:
            result = stable_residue(args.q, args.precision)
    except ValueError as exc:
        parser.error(str(exc))
    print(result)


if __name__ == "__main__":
    main()
