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


def even_count_stream(a: int, q: int, max_n: int) -> Iterator[int]:
    """Stream v_(a,q)(2n) for 0 <= n <= max_n by the exact nonlinear update.

    The state is the triple (t, h, value) with t = T_(a,q)(n) and
    h = gap(a,q,t).  Advancing n by one costs a single exact comparison
    h < a**n, one multiplication of h by q, and at most one multiplication
    of the running count by a.  No logarithm is evaluated anywhere.

    This is the executable form of the streaming recurrence in the article.
    """
    check_bases(a, q)
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    yield 1  # n = 0: the empty product has the single coefficient 1
    if max_n == 0:
        return
    t = threshold(a, q, 1)
    h = gap(a, q, t)
    a_power = a  # a**n for the current n
    exponent_e = max(0, 1 - t)
    value = 2 * a**exponent_e
    yield value
    for n in range(2, max_n + 1):
        a_power *= a
        if h < a_power:
            t += 1
            h = q * h - (a - 1)
        new_e = max(0, n - t)
        if new_e - exponent_e not in (0, 1):
            raise ArithmeticError("Threshold increments must lie in {0,1}")
        if new_e > exponent_e:
            value *= a
            exponent_e = new_e
        yield value


def ternary_even_without_logs(n: int) -> int:
    """v_(2,3)(2n), computed by a deliberately different integer route.

    Instead of the gap threshold, this finds the least s with 3**s >= 2**(n+1)
    and returns 2**(n+1-s).  It is an independent implementation of the floor
    formula, used only to cross-check the gap-based computation.
    """
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    if n < 2:
        return 1 << n
    target, power, s = 1 << (n + 1), 1, 0
    while power < target:
        power *= 3
        s += 1
    return 1 << (n + 1 - s)


def exceptional_parity_indices(a: int, q: int, limit: int) -> List[int]:
    """The finite set {n >= 1 : T_(a,q)(n+1) > n}, searched up to `limit`."""
    check_bases(a, q)
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    return [n for n in range(1, limit + 1) if threshold(a, q, n + 1) > n]


def full_from_even(a: int, q: int, N: int) -> int:
    """v_(a,q)(N) from the even--odd identity, never from the odd rectangle.

    Even N is delegated to the closed formula.  Odd N uses the general
    parity identity: the odd count is the next even count divided by a,
    except at the finitely many indices where the threshold saturates.
    """
    check_bases(a, q)
    if N < 0:
        raise ValueError("N must be nonnegative")
    if N % 2 == 0:
        return interleaved_count(a, q, N)
    n = N // 2
    if n == 0:
        return a
    if threshold(a, q, n + 1) > n:
        return 2
    return interleaved_count(a, q, 2 * n + 2) // a


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


def dense_coefficients(a: int, q: int, m: int, n: int,
                       max_degree: int = 4_000_000) -> List[int]:
    """Expand the defining polynomial, without using interval or gap formulas."""
    check_bases(a, q)
    if m < 0 or n < 0:
        raise ValueError("m and n must be nonnegative")
    degree = (a - 1) * ((a**m - 1) // (a - 1) if a > 1 else 0)
    degree += (a - 1) * sum(q**j for j in range(n))
    if degree > max_degree:
        raise ValueError(f"Dense expansion of degree {degree} exceeds max_degree")
    coefficients = [1]
    for j in range(m):
        coefficients = multiply_digit_factor(coefficients, a**j, a)
    for j in range(n):
        coefficients = multiply_digit_factor(coefficients, q**j, a)
    return coefficients


def digit_support(a: int, q: int, n: int, max_size: int = 1 << 22) -> List[int]:
    """Sorted q-adic integers with n digits drawn from 0,...,a-1.

    The explicit enumeration has a**n entries; `max_size` guards against
    an accidental request that would exhaust memory.
    """
    check_bases(a, q)
    if n < 0:
        raise ValueError("n must be nonnegative")
    if a**n > max_size:
        raise ValueError(f"Explicit digit support of size {a}**{n} exceeds max_size")
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
