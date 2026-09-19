#!/usr/bin/env python3
"""Exact coefficient-one counts for the mixed-base product family.

Python 3.9+; standard library only. All mathematical decisions use integers.
For 2 <= a < q, let D_a(y) = 1 + y + ... + y**(a-1).
The rectangular product is
    prod_{j<m} D_a(x**(a**j)) * prod_{j<n} D_a(x**(q**j)).
"""
from collections import Counter
from typing import Dict, Iterator, List, Tuple


def check_bases(a: int, q: int) -> None:
    if not isinstance(a, int) or not isinstance(q, int) or not 2 <= a < q:
        raise ValueError("Expected integer bases 2 <= a < q")


def gap(a: int, q: int, t: int) -> int:
    """Gap after a carry through t maximal digits."""
    check_bases(a, q)
    if t < 0:
        raise ValueError("t must be nonnegative")
    numerator = (q - a) * q**t + a - 1
    value, remainder = divmod(numerator, q - 1)
    if remainder:
        raise ArithmeticError("The gap numerator must be divisible by q-1")
    return value


def threshold(a: int, q: int, m: int) -> int:
    """Least t >= 0 such that gap(a,q,t) >= a**m; no logarithms."""
    check_bases(a, q)
    if m < 0:
        raise ValueError("m must be nonnegative")
    target = (q - 1) * a**m
    power, t = 1, 0
    while (q - a) * power + a - 1 < target:
        power *= q
        t += 1
    return t


def threshold_stream(a: int, q: int, stop: int) -> Iterator[Tuple[int, int, int]]:
    """Yield (m,T(m),q**T(m)), 0 <= m <= stop, with shared work."""
    check_bases(a, q)
    if stop < 0:
        raise ValueError("stop must be nonnegative")
    a_power, q_power, t = 1, 1, 0
    for m in range(stop + 1):
        target = (q - 1) * a_power
        while (q - a) * q_power + a - 1 < target:
            q_power *= q
            t += 1
        yield m, t, q_power
        a_power *= a


def count_one(a: int, q: int, m: int, n: int) -> int:
    """Closed formula, including the empty-factor boundary cases."""
    check_bases(a, q)
    if m < 0 or n < 0:
        raise ValueError("m and n must be nonnegative")
    if n == 0:
        return a**m
    if m == 0:
        return a**n
    return 2 * a**max(0, n - threshold(a, q, m))


def exponent(a: int, q: int, index: int) -> int:
    """G_index, where G_(2j+1)=a**j and G_(2j+2)=q**j."""
    check_bases(a, q)
    if index < 1:
        raise ValueError("index must be positive")
    return (a if index % 2 else q) ** ((index - 1) // 2)


def interleaved_count(a: int, q: int, N: int) -> int:
    if N < 0:
        raise ValueError("N must be nonnegative")
    return count_one(a, q, (N + 1) // 2, N // 2)


def multiply_digit_factor(coefficients: List[int], weight: int, a: int) -> List[int]:
    """Schoolbook polynomial multiplication; independent of the formula."""
    if weight < 1 or a < 2:
        raise ValueError("weight >= 1 and a >= 2 are required")
    result = [0] * (len(coefficients) + (a - 1) * weight)
    for digit in range(a):
        offset = digit * weight
        for j, value in enumerate(coefficients):
            result[j + offset] += value
    return result


def dense_coefficients(a: int, q: int, m: int, n: int) -> List[int]:
    """Expand the defining polynomial, without using interval or gap formulas."""
    check_bases(a, q)
    if m < 0 or n < 0:
        raise ValueError("m and n must be nonnegative")
    coefficients = [1]
    for j in range(m):
        coefficients = multiply_digit_factor(coefficients, a**j, a)
    for j in range(n):
        coefficients = multiply_digit_factor(coefficients, q**j, a)
    return coefficients


def digit_support(a: int, q: int, n: int) -> List[int]:
    """Sorted q-adic integers with n digits drawn from 0,...,a-1."""
    check_bases(a, q)
    if n < 0:
        raise ValueError("n must be nonnegative")
    support = [0]
    power = 1
    for _ in range(n):
        support = [digit * power + s for digit in range(a) for s in support]
        power *= q
    return support


def interval_histogram(a: int, q: int, m: int, n: int) -> Dict[int, int]:
    """Count every coefficient value by an independent endpoint-event sweep.

    The list of starts and the translated list of ends are already sorted.
    This uses O(a**n) events instead of expanding a degree Theta(q**n) polynomial.
    Histogram key 0 counts zero coefficients between exponent 0 and the degree.
    """
    check_bases(a, q)
    if m < 0 or n < 0:
        raise ValueError("m and n must be nonnegative")
    support = digit_support(a, q, n)
    length = a**m
    events = Counter(support)
    events.subtract(s + length for s in support)
    histogram = Counter()  # type: Counter[int]
    previous, active = 0, 0
    for point, delta in sorted(events.items()):
        if point > previous:
            histogram[active] += point - previous
        active += delta
        if active < 0:
            raise ArithmeticError("Interval coverage cannot be negative")
        previous = point
    if active != 0:
        raise ArithmeticError("Coverage must return to zero")
    return dict(histogram)


if __name__ == "__main__":
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", default=40,
                        help="largest prefix index to print (default: 40)")
    parser.add_argument("--a", type=int, default=2)
    parser.add_argument("--q", type=int, default=3)
    args = parser.parse_args()
    if args.N < 0:
        parser.error("N must be nonnegative")
    print(json.dumps([interleaved_count(args.a, args.q, N)
                      for N in range(args.N + 1)]))
