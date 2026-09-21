"""Exact Motzkin arithmetic and prime-modulus evaluation (Python 3.9+).

No third-party packages. The prime-modulus evaluator uses a proved Lucas rule
for central trinomial coefficients, followed by
    2 M_n = 3 T_n + 2 T_(n+1) - T_(n+2).
The exact recurrences never replace a noninvertible division by a modular one.
"""
from __future__ import annotations

import argparse
from math import comb, isqrt
from typing import List, Optional, Sequence


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def primes_up_to(limit: int) -> List[int]:
    return [p for p in range(2, limit + 1) if is_prime(p)]


def motzkin_numbers(limit: int) -> List[int]:
    """Return exact M_0,...,M_limit using integer arithmetic."""
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    values = [1] if limit == 0 else [1, 1]
    for n in range(2, limit + 1):
        value, remainder = divmod(
            (2 * n + 1) * values[-1] + 3 * (n - 1) * values[-2], n + 2
        )
        if remainder:
            raise ArithmeticError("Motzkin recurrence division was not exact")
        values.append(value)
    return values


def central_trinomial_numbers(limit: int) -> List[int]:
    """Return exact T_0,...,T_limit."""
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    values = [1] if limit == 0 else [1, 1]
    for n in range(2, limit + 1):
        value, remainder = divmod(
            (2 * n - 1) * values[-1] + 3 * (n - 1) * values[-2], n
        )
        if remainder:
            raise ArithmeticError("Trinomial recurrence division was not exact")
        values.append(value)
    return values


def motzkin_binomial(n: int) -> int:
    """Independent exact formula, convenient for small cross-checks."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return sum(comb(n, 2 * j) * (comb(2 * j, j) // (j + 1))
               for j in range(n // 2 + 1))


def trinomial_binomial(n: int) -> int:
    if n < 0:
        raise ValueError("n must be nonnegative")
    return sum(comb(n, 2 * j) * comb(2 * j, j)
               for j in range(n // 2 + 1))


def trinomial_prime_table(p: int) -> List[int]:
    """T_0,...,T_(p-1) mod p in O(p) field operations and space.

    The modular inverse recurrence uses 1 <= n < p only.
    """
    if not is_prime(p):
        raise ValueError("p must be prime")
    values = [1] * p
    inverses = [0] * p
    inverses[1] = 1
    for n in range(2, p):
        inverses[n] = (-(p // n) * inverses[p % n]) % p
        values[n] = ((2 * n - 1) * values[n - 1]
                     + 3 * (n - 1) * values[n - 2]) * inverses[n] % p
    return values


def trinomial_mod_prime(n: int, p: int,
                        table: Optional[Sequence[int]] = None) -> int:
    """Evaluate T_n mod p by multiplying the entries for the base-p digits."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if table is None:
        table = trinomial_prime_table(p)
    elif p < 2 or len(table) != p:
        raise ValueError("table must contain exactly p residues for a prime p")
    result = 1
    while n:
        n, digit = divmod(n, p)
        result = result * table[digit] % p
    return result


def motzkin_mod_prime(n: int, p: int,
                     table: Optional[Sequence[int]] = None) -> int:
    """Evaluate M_n mod an odd prime without constructing M_n itself.

    A supplied table must be the output of trinomial_prime_table(p).
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    if p < 3 or p % 2 == 0:
        raise ValueError("p must be an odd prime")
    if table is None:
        table = trinomial_prime_table(p)
    t0 = trinomial_mod_prime(n, p, table)
    t1 = trinomial_mod_prime(n + 1, p, table)
    t2 = trinomial_mod_prime(n + 2, p, table)
    return (3 * t0 + 2 * t1 - t2) * ((p + 1) // 2) % p


def block_mod_prime_power(m: int, k: int, offset: int,
                          p: int, precision: int) -> int:
    """Evaluate M_(m*p**k+offset) mod p**precision in the proved small block.

    Requires 1 <= precision <= k and 0 <= offset < p**(k-precision+1).
    This implementation constructs only local exact coefficients, not the
    generally much larger target Motzkin number. Its cost grows with
    max(offset, m*p**(precision-1)); it is not a general-purpose fast
    algorithm for arbitrary prime powers.
    """
    if not is_prime(p) or p == 2:
        raise ValueError("p must be an odd prime")
    if m < 0 or not (1 <= precision <= k):
        raise ValueError("require m >= 0 and 1 <= precision <= k")
    q = p ** (k - precision + 1)
    if not (0 <= offset < q):
        raise ValueError("offset lies outside the proved block")
    h = m * p ** (precision - 1)
    ts = central_trinomial_numbers(h + 1)
    u = (ts[h + 1] - ts[h]) // 2
    value = ts[h] * motzkin_numbers(offset)[offset]
    if offset == q - 2:
        value -= u
    elif offset == q - 1:
        value -= (q - 1) * u
    return value % (p ** precision)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    exact = commands.add_parser("exact", help="Print an exact Motzkin number")
    exact.add_argument("n", type=int)
    modular = commands.add_parser("mod", help="Print M_n modulo an odd prime")
    modular.add_argument("n", type=int)
    modular.add_argument("p", type=int)
    block = commands.add_parser("block", help="Use the prime-power block theorem")
    for name in ["m", "k", "offset", "p", "precision"]:
        block.add_argument(name, type=int)
    args = parser.parse_args()
    try:
        if args.command == "exact":
            print(motzkin_numbers(args.n)[args.n])
        elif args.command == "mod":
            print(motzkin_mod_prime(args.n, args.p))
        else:
            print(block_mod_prime_power(args.m, args.k, args.offset,
                                        args.p, args.precision))
    except (ValueError, ArithmeticError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
