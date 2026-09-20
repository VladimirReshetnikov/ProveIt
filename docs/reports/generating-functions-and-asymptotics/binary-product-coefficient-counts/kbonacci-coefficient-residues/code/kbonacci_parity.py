"""Exact algorithms accompanying 'Odd coefficients in quasifibonacci products'.

Python 3.10+, standard library only. All polynomial/count arithmetic is integral.
Public indices: weights/signs are zero-based lists; n is a number of factors.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Sequence
from math import prod


def _integer(value: int, name: str, minimum: int = 0) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def standard_seeds(k: int) -> list[int]:
    """Return F_k,...,F_(2k-1), with F_1=...=F_k=1."""
    _integer(k, "k", 2)
    return [1] + [(k - 1) * (1 << (i - 2)) + 1 for i in range(2, k + 1)]


def check_seeds(seeds: Sequence[int]) -> list[int]:
    values = list(seeds)
    _integer(len(values), "number of seeds", 2)
    total = 0
    for i, value in enumerate(values, 1):
        _integer(value, f"seed {i}", 1)
        if value <= total:
            raise ValueError(f"seed {i} must exceed the sum {total} of earlier seeds")
        total += value
    return values


def weights(k: int, n: int, seeds: Sequence[int] | None = None) -> list[int]:
    """Return n positive quasifibonacci weights; initial seeds are superincreasing."""
    _integer(k, "k", 2)
    _integer(n, "n")
    a = check_seeds(standard_seeds(k) if seeds is None else seeds)
    if len(a) != k:
        raise ValueError("exactly k seeds are required")
    total = sum(a)
    while len(a) < n:
        outgoing = a[-k]
        a.append(total)
        total += a[-1] - outgoing
    return a[:n]


def coherent_signs(k: int, n: int, initial: Sequence[int] | None = None) -> list[int]:
    """Signs repeat a length-(k+1) block with product -1.

    Default: k plus signs, then a minus sign, repeated.
    """
    _integer(k, "k", 2)
    _integer(n, "n")
    a = [1] * k if initial is None else list(initial)
    if len(a) != k or any(isinstance(x, bool) or not isinstance(x, int) or x not in (-1, 1)
                          for x in a):
        raise ValueError("initial must contain exactly k signs, each -1 or +1")
    block = a + [-prod(a)]
    return [block[i % (k + 1)] for i in range(n)]


def count_prefix(k: int, n: int, modulus: int | None = None) -> list[int]:
    """h_k(0),...,h_k(n), from the proved order-(k+1) recurrence."""
    _integer(k, "k", 2)
    _integer(n, "n")
    if modulus is not None:
        _integer(modulus, "modulus", 1)
    values = [1 << i for i in range(min(k, n) + 1)]
    if modulus is not None:
        values = [x % modulus for x in values]
    for i in range(k + 1, n + 1):
        value = 2 * (values[i - 1] - values[i - k] + values[i - k - 1])
        values.append(value if modulus is None else value % modulus)
    return values


def count_fast(k: int, n: int, modulus: int | None = None) -> int:
    """Compute h_k(n) in O(k^2 log(n+1)) ring operations.

    Binary polynomial powering modulo X^(k+1)-2X^k+2X-2.
    This is arithmetic-operation complexity, not a bit-complexity claim.
    """
    _integer(k, "k", 2)
    _integer(n, "n")
    if modulus is not None:
        _integer(modulus, "modulus", 1)
    if n <= k:
        return (1 << n) if modulus is None else pow(2, n, modulus)
    d = k + 1

    def multiply(a: list[int], b: list[int]) -> list[int]:
        out = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i + j] += x * y
        for p in range(2 * d - 2, d - 1, -1):
            c = out[p] if modulus is None else out[p] % modulus
            # X^d = 2 X^k - 2 X + 2.
            out[p - 1] += 2 * c
            out[p - k] -= 2 * c
            out[p - k - 1] += 2 * c
        return out[:d] if modulus is None else [x % modulus for x in out[:d]]

    accumulator = [1] + [0] * (d - 1)
    power = [0, 1] + [0] * (d - 2)
    exponent = n
    while exponent:
        if exponent & 1:
            accumulator = multiply(accumulator, power)
        exponent >>= 1
        if exponent:
            power = multiply(power, power)
    value = sum(c * (1 << i) for i, c in enumerate(accumulator))
    return value if modulus is None else value % modulus


def parity_bitset(a: Sequence[int], max_degree: int = 8_000_000) -> int:
    """Direct product in F_2[x], encoded as a Python integer.

    The coefficient of x^m is (result >> m) & 1. The degree cap prevents
    accidental exponential memory allocation; it does not affect count_fast.
    """
    _integer(max_degree, "max_degree")
    for i, value in enumerate(a):
        _integer(value, f"weight {i}", 1)
    if sum(a) > max_degree:
        raise ValueError("degree cap exceeded for direct bitset expansion")
    bits = 1
    for value in a:
        bits ^= bits << value
    return bits


def signed_sparse(a: Sequence[int], signs: Sequence[int]) -> dict[int, int]:
    """Direct sparse integer multiplication, for small independent checks."""
    if len(a) != len(signs):
        raise ValueError("weights and signs must have equal length")
    coefficients = {0: 1}
    for value, sign in zip(a, signs):
        _integer(value, "weight", 1)
        if isinstance(sign, bool) or not isinstance(sign, int) or sign not in (-1, 1):
            raise ValueError("each sign must be -1 or +1")
        updated = coefficients.copy()
        for exponent, coefficient in coefficients.items():
            target = exponent + value
            updated[target] = updated.get(target, 0) + sign * coefficient
        coefficients = {m: c for m, c in updated.items() if c}
    return coefficients


class CoefficientOracle:
    """Single-branch O(n)-step evaluation of a coherently signed coefficient.

    Construction uses O(n+k)-entry preprocessing, including seed validation. parity(m) also gives the parity
    of [x^m] prod(1+x^w_i). No exponentially large polynomial is allocated.
    """

    def __init__(self, k: int, n: int, seeds: Sequence[int] | None = None,
                 initial_signs: Sequence[int] | None = None) -> None:
        self.k = k
        self.n = n
        self.w = [0] + weights(k, n, seeds)
        self.e = [1] + coherent_signs(k, n, initial_signs)
        self.s = [0]
        for value in self.w[1:]:
            self.s.append(self.s[-1] + value)

    def signed(self, exponent: int) -> int:
        if isinstance(exponent, bool) or not isinstance(exponent, int):
            raise ValueError("exponent must be an integer")
        n, m, multiplier = self.n, exponent, 1
        if m < 0 or m > self.s[n]:
            return 0
        while n > self.k:
            if m < self.w[n]:
                n -= 1
            elif m > self.s[n - 1]:
                multiplier *= self.e[n]
                m -= self.w[n]
                n -= 1
            else:
                j = n - self.k - 1
                u = m - self.w[n]
                v = self.w[j + 1]
                multiplier *= self.e[n] * self.e[j + 1]
                if u >= v:
                    m = u - v
                elif u + v <= self.s[j]:
                    m = u + v
                    multiplier = -multiplier
                else:
                    return 0
                n = j
        # The superincreasing seed block has a unique greedy representation.
        while n:
            if m >= self.w[n]:
                m -= self.w[n]
                multiplier *= self.e[n]
            n -= 1
        return multiplier if m == 0 else 0

    def parity(self, exponent: int) -> int:
        return abs(self.signed(exponent))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k", type=int)
    parser.add_argument("n", type=int)
    parser.add_argument("--modulus", type=int)
    parser.add_argument("--prefix", action="store_true")
    parser.add_argument("--coefficient", type=int,
                        help="query a coefficient's parity for standard seeds")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    try:
        if args.coefficient is not None:
            oracle = CoefficientOracle(args.k, args.n)
            value = {"parity": oracle.parity(args.coefficient),
                     "signed_coefficient": oracle.signed(args.coefficient)}
        elif args.prefix:
            value = count_prefix(args.k, args.n, args.modulus)
        else:
            value = count_fast(args.k, args.n, args.modulus)
        print(json.dumps(value))
    except ValueError as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()
