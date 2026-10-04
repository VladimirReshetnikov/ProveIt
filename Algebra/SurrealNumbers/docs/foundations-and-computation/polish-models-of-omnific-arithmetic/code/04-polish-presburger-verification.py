#!/usr/bin/env python3
"""Exact finite checks and a stream implementation for Polish Presburger models.

Python 3.10+, standard library only.  The tests are not a proof of the infinite
or topological theorems.  Infinite streams are represented by indexed oracles;
every returned output coordinate uses finitely many input coordinates.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random
from typing import Callable, Generic, TypeVar

T = TypeVar('T')

class Stream(Generic[T]):
    """Memoized total indexed oracle. Totality is a contract of the caller."""
    def __init__(self, get: Callable[[int], T]):
        self._get = lru_cache(maxsize=None)(get)
    def __getitem__(self, n: int) -> T:
        if not isinstance(n, int) or n < 0:
            raise ValueError('stream indices must be nonnegative integers')
        return self._get(n)
    def prefix(self, length: int) -> list[T]:
        return [self[i] for i in range(length)]


def z_encode(z: int) -> int:
    return 2 * z - 1 if z > 0 else -2 * z


def z_decode(n: int) -> int:
    if n < 0:
        raise ValueError('natural code required')
    return (n + 1) // 2 if n % 2 else -(n // 2)


def positive_encode(x: Q) -> int:
    """Positive rationals <-> positive integers, by the Calkin--Wilf tree."""
    if x <= 0:
        raise ValueError('positive rational required')
    p, q = x.numerator, x.denominator
    reverse_path: list[int] = []
    while p != q:
        if p > q:
            reverse_path.append(1)
            p -= q
        else:
            reverse_path.append(0)
            q -= p
    result = 1
    for bit in reversed(reverse_path):
        result = 2 * result + bit
    return result


def positive_decode(n: int) -> Q:
    if n <= 0:
        raise ValueError('positive integer code required')
    p, q = 1, 1
    for bit in bin(n)[3:]:
        if bit == '1':
            p += q
        else:
            q += p
    return Q(p, q)


def q_encode(x: Q) -> int:
    if not x:
        return 0
    r = positive_encode(abs(x))
    return 2 * r - 1 if x > 0 else 2 * r


def q_decode(n: int) -> Q:
    if n < 0:
        raise ValueError('natural code required')
    if not n:
        return Q(0)
    return positive_decode((n + 1) // 2) if n % 2 else -positive_decode(n // 2)


def pair(a: int, b: int) -> int:
    if a < 0 or b < 0:
        raise ValueError('natural pair required')
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    if n < 0:
        raise ValueError('natural code required')
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


@dataclass(frozen=True)
class StreamElement:
    coefficients: Stream[Q]
    integer: int
    # Contract: the coefficient stream is lexicographically positive, or is
    # identically zero and integer >= 0. This is not a decidable validation.


def decode_baire(code: Stream[int]) -> StreamElement:
    z = z_decode(code[0])
    if z < 0:
        k, r = unpair(code[1])
        leading = positive_decode(r + 1)
        def get(i: int) -> Q:
            if i < k:
                return Q(0)
            if i == k:
                return leading
            return q_decode(code[1 + i - k])
    else:
        def get(i: int) -> Q:
            for j in range(i + 1):
                value = code[1 + j]
                if value:
                    return positive_decode(value) if j == i else q_decode(code[1 + i])
            return Q(0)
    return StreamElement(Stream(get), z)


def encode_baire(x: StreamElement) -> Stream[int]:
    d, z = x.coefficients, x.integer
    @lru_cache(maxsize=1)
    def first_positive() -> tuple[int, Q]:
        k = 0
        while not d[k]:
            k += 1
        if d[k] < 0:
            raise ValueError('element violates the positive-cone contract')
        return k, d[k]
    def get(i: int) -> int:
        if i == 0:
            return z_encode(z)
        if z < 0:
            k, leading = first_positive()  # Terminates by the contract.
            return pair(k, positive_encode(leading) - 1) if i == 1 else q_encode(d[k + i - 1])
        j = i - 1
        for k in range(j + 1):
            if d[k]:
                if d[k] < 0:
                    raise ValueError('element violates the positive-cone contract')
                return positive_encode(d[k]) if k == j else q_encode(d[j])
        return 0
    return Stream(get)


def baire_add(a: Stream[int], b: Stream[int]) -> Stream[int]:
    x, y = decode_baire(a), decode_baire(b)
    d = Stream(lambda i: x.coefficients[i] + y.coefficients[i])
    return encode_baire(StreamElement(d, x.integer + y.integer))


def baire_quotient(a: Stream[int], m: int) -> Stream[int]:
    if m <= 0:
        raise ValueError('positive standard divisor required')
    x = decode_baire(a)
    return encode_baire(StreamElement(Stream(lambda i: x.coefficients[i] / m), x.integer // m))


def baire_remainder(a: Stream[int], m: int) -> Stream[int]:
    if m <= 0:
        raise ValueError('positive standard divisor required')
    x = decode_baire(a)
    return encode_baire(StreamElement(Stream(lambda i: Q(0)), x.integer % m))


@dataclass(frozen=True, order=True)
class Element:
    """Finite-support rational model; tuple order implements lexicographic order."""
    coefficients: tuple[Q, ...]
    integer: int
    def __add__(self, other: Element) -> Element:
        if len(self.coefficients) != len(other.coefficients):
            raise ValueError('dimensions differ')
        return Element(tuple(x + y for x, y in zip(self.coefficients, other.coefficients)),
                       self.integer + other.integer)
    def __neg__(self) -> Element:
        return Element(tuple(-x for x in self.coefficients), -self.integer)
    def __sub__(self, other: Element) -> Element:
        return self + (-other)
    def scale(self, n: int) -> Element:
        return Element(tuple(n * x for x in self.coefficients), n * self.integer)
    def divide(self, m: int) -> tuple[Element, int]:
        if m <= 0:
            raise ValueError('positive divisor required')
        return Element(tuple(x / m for x in self.coefficients), self.integer // m), self.integer % m


def numeral(n: int, dimension: int) -> Element:
    return Element((Q(0),) * dimension, n)


def candidates(lower: list[Element], upper: list[Element], m: int, dimension: int) -> list[Element]:
    if m <= 0:
        raise ValueError('positive modulus required')
    if lower:
        base = max(lower)
        return [base + numeral(s, dimension) for s in range(1, m + 1)]
    if upper:
        base = min(upper)
        return [base - numeral(s, dimension) for s in range(1, m + 1)]
    return [numeral(s, dimension) for s in range(m)]


def satisfies(x: Element, lower: list[Element], upper: list[Element],
              m: int, allowed: set[int]) -> bool:
    return all(a < x for a in lower) and all(x < b for b in upper) and x.integer % m in allowed


def matrix_apply(matrix: list[list[Q]], x: tuple[Q, ...]) -> tuple[Q, ...]:
    return tuple(sum((a * b for a, b in zip(row, x)), Q(0)) for row in matrix)


def run_tests(seed: int = 20261003) -> dict[str, object]:
    rng = random.Random(seed)
    checks: Counter[str] = Counter()
    def check(condition: bool, category: str) -> None:
        if not condition:
            raise AssertionError(f'failed test in {category}; seed={seed}')
        checks[category] += 1

    for n in range(2001):
        check(q_encode(q_decode(n)) == n, 'rational_codes')
        check(z_encode(z_decode(n)) == n, 'integer_codes')
        check(pair(*unpair(n)) == n, 'pairing_codes')
    for p in range(-15, 16):
        for q in range(1, 16):
            x = Q(p, q)
            check(q_decode(q_encode(x)) == x, 'rational_codes')

    dimension = 2
    values = [Q(-1), Q(0), Q(1, 2), Q(1)]
    pool = [Element(d, z) for d in product(values, repeat=dimension) for z in range(-4, 5)]
    zero, one = numeral(0, dimension), numeral(1, dimension)
    for x in pool:
        check(x + (-x) == zero, 'group_and_order')
        if x > zero:
            check(x >= one, 'group_and_order')
        for m in range(1, 10):
            q, r = x.divide(m)
            check(q.scale(m) + numeral(r, dimension) == x and 0 <= r < m, 'division')
            if x >= zero:
                check(q >= zero, 'division')
    for _ in range(4000):
        x, y, z = (rng.choice(pool) for _ in range(3))
        check((x + y) + z == x + (y + z), 'group_and_order')
        check((x < y) == (x + z < y + z), 'group_and_order')
        if x >= zero and y >= zero:
            check(x + y >= zero, 'group_and_order')

    # Exhaustive witnesses in the chosen finite pool; the candidate set is
    # added to the comparison pool. This is not exhaustive over the group.
    for _ in range(1200):
        lower = [rng.choice(pool) for _ in range(rng.randrange(4))]
        upper = [rng.choice(pool) for _ in range(rng.randrange(4))]
        m = rng.randrange(1, 10)
        allowed = {r for r in range(m) if rng.randrange(2)}
        cs = candidates(lower, upper, m, dimension)
        finite_answer = any(satisfies(x, lower, upper, m, allowed) for x in cs)
        for x in pool:
            if satisfies(x, lower, upper, m, allowed):
                check(finite_answer, 'boundary_witness_transfer')
        extended_answer = any(satisfies(x, lower, upper, m, allowed) for x in pool + cs)
        check(finite_answer == extended_answer, 'boundary_finite_comparison')

    for m in range(1, 17):
        for x in pool:
            external_p = lambda a: any(a.coefficients)
            check(external_p(x + numeral(m, dimension)) == external_p(x), 'periodicity_counterexample')
        check(not any(any(numeral(r, dimension).coefficients) for r in range(m)),
              'periodicity_counterexample')
    check(any(any(x.coefficients) for x in pool), 'periodicity_counterexample')

    for _ in range(150):
        n, rows = 6, 13
        pivots = sorted(rng.sample(range(rows), n))
        matrix = [[Q(0) for _ in range(n)] for _ in range(rows)]
        for k, p in enumerate(pivots):
            matrix[p][k] = Q(rng.randrange(1, 5), rng.randrange(1, 5))
            for i in range(p + 1, rows):
                matrix[i][k] = Q(rng.randrange(-4, 5), rng.randrange(1, 5))
        for _ in range(40):
            x = tuple(Q(rng.randrange(-3, 4)) for _ in range(n))
            y = tuple(Q(rng.randrange(-3, 4)) for _ in range(n))
            tx, ty = matrix_apply(matrix, x), matrix_apply(matrix, y)
            check((x < y) == (tx < ty), 'pivot_matrices')
            check(matrix_apply(matrix, tuple(a + b for a, b in zip(x, y))) ==
                  tuple(a + b for a, b in zip(tx, ty)), 'pivot_matrices')
            recovered: list[Q] = []
            for k, p in enumerate(pivots):
                recovered.append((tx[p] - sum((matrix[p][j] * recovered[j] for j in range(k)), Q(0))) /
                                 matrix[p][k])
            check(tuple(recovered) == x, 'pivot_matrices')

    # Exact representatives of the two monus discontinuity sequences.
    for m in range(5):
        for n in range(5):
            if m == n:
                continue
            x, y = numeral(m, 1), numeral(n, 1)
            base = max(x - y, numeral(0, 1))
            for j in range(1, 21):
                u = Element((Q(1, j),), 0)
                value = max(x + u - y, numeral(0, 1)) if m < n else max(x - y - u, numeral(0, 1))
                check(value.integer != base.integer, 'monus_integer_obstruction')

    # Deterministic infinite oracles. Long initial zero runs test the boundary
    # at the zero coefficient stream as well as the positive charts.
    codes: list[Stream[int]] = [Stream(lambda i: 0)]
    for sample in range(96):
        first = rng.randrange(31)
        delay = rng.randrange(35)
        salt = rng.randrange(1, 10000)
        codes.append(Stream(lambda i, first=first, delay=delay, salt=salt:
                            first if i == 0 else (0 if i <= delay else ((i * 13 + salt) % 31))))
    prefix_length = 40
    for code in codes:
        x = decode_baire(code)
        rebuilt = encode_baire(x)
        check(rebuilt.prefix(prefix_length) == code.prefix(prefix_length), 'baire_roundtrip')
        for m in (1, 2, 3, 7):
            q = decode_baire(baire_quotient(code, m))
            r = decode_baire(baire_remainder(code, m))
            check(q.integer * m + r.integer == x.integer and 0 <= r.integer < m, 'baire_division')
            for i in range(24):
                check(q.coefficients[i] * m + r.coefficients[i] == x.coefficients[i], 'baire_division')
    for _ in range(150):
        a, b = rng.choice(codes), rng.choice(codes)
        x, y = decode_baire(a), decode_baire(b)
        summed = decode_baire(baire_add(a, b))
        check(summed.integer == x.integer + y.integer, 'baire_addition')
        for i in range(24):
            check(summed.coefficients[i] == x.coefficients[i] + y.coefficients[i], 'baire_addition')

    return {
        'status': 'passed', 'seed': seed, 'total_assertions': sum(checks.values()),
        'assertions_by_category': dict(sorted(checks.items())),
        'scope': 'Exact rational finite tests and finite-prefix stream checks; not a formal proof.',
        'stream_prefix_length': prefix_length,
        'third_party_dependencies': [],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=20261003)
    parser.add_argument('--output', type=Path, default=Path('verification_results.json'))
    args = parser.parse_args()
    result = run_tests(args.seed)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
