#!/usr/bin/env python3
"""Verify archived A202058 data and independent finite enumerations."""
from collections import Counter, defaultdict
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path
from fractions import Fraction
from math import factorial, comb
import argparse
import re
import sys

HERE = Path(__file__).resolve().parent

class VerificationError(ValueError):
    """An input or mathematical check failed; active even under python -O."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def nonnegative_integer(token, location):
    require(re.fullmatch(r'[0-9]+', token) is not None,
            f'{location}: expected a nonnegative decimal integer, got {token!r}')
    return int(token)


def data_rows(path):
    path = Path(path)
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        stripped = line.strip()
        if stripped and not stripped.startswith('#'):
            yield f'{path}:{line_number}', stripped.split()


def exact_file(path):
    result = {}
    for location, fields in data_rows(path):
        require(len(fields) == 2, f'{location}: expected exactly two columns')
        n = nonnegative_integer(fields[0], location)
        value = nonnegative_integer(fields[1], location)
        require(value > 0, f'{location}: coefficient must be positive')
        require(n not in result, f'{location}: duplicate index {n}')
        result[n] = value
    require(bool(result), f'{path}: no coefficient rows')
    return result


def contiguous_indices(values, first, last, description):
    expected = set(range(first, last + 1))
    missing = sorted(expected - values.keys())
    extra = sorted(values.keys() - expected)
    require(not missing and not extra,
            f'{description}: expected every index {first}..{last} exactly once; '
            f'missing={missing[:8]}, extra={extra[:8]}')


def matching_coefficients(values, archived, description):
    for n, value in values.items():
        require(n in archived, f'{description}: unsupported index {n}')
        require(value == archived[n], f'{description}: wrong coefficient at n={n}')


def numerical_file(path, maximum=1200):
    result = {}
    for location, fields in data_rows(path):
        require(len(fields) == 5, f'{location}: expected exactly five columns')
        n = nonnegative_integer(fields[0], location)
        require(n not in result, f'{location}: duplicate index {n}')
        try:
            numbers = tuple(Decimal(value) for value in fields[1:])
        except InvalidOperation as error:
            raise VerificationError(f'{location}: invalid decimal number') from error
        require(all(value.is_finite() for value in numbers),
                f'{location}: all numerical entries must be finite')
        require(numbers[1] > 0, f'{location}: ratio must be positive')
        result[n] = numbers
    contiguous_indices(result, 1, maximum, str(path))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rebuilt', help='Path to freshly generated exact output')
    parser.add_argument('--expected-max', type=int,
                        help='Required with --rebuilt: its exact final index (0..395)')
    args = parser.parse_args()
    if (args.rebuilt is None) != (args.expected_max is None):
        parser.error('--rebuilt and --expected-max must be supplied together')
    if args.expected_max is not None and not 0 <= args.expected_max <= 395:
        parser.error('--expected-max must be between 0 and 395')
    archived = exact_file(HERE / 'exact_coefficients_395.txt')
    oeis = exact_file(HERE / 'oeis_b202058.txt')
    contiguous_indices(archived, 0, 395, 'Archived exact table')
    contiguous_indices(oeis, 0, 176, 'OEIS table')
    matching_coefficients(oeis, archived, 'OEIS table')
    if args.rebuilt is not None:
        rebuilt = exact_file(args.rebuilt)
        contiguous_indices(rebuilt, 0, args.expected_max, 'Fresh GMP table')
        matching_coefficients(rebuilt, archived, 'Fresh GMP table')
        print(f'Fresh GMP transfer agrees on all indices 0..{args.expected_max}')

    polynomial_history = [Counter()]
    states = {(1, 1, 1): 1}
    words = [(0,)]
    for n in range(1, 10):
        actual = Counter()
        for word in words:
            counts = Counter(word)
            singletons = sum(value == 1 for value in counts.values())
            ascents = sum(a < b for a, b in zip(word, word[1:]))
            actual[singletons, ascents + 2 - len(counts)] += 1
        compact = Counter()
        for (m, h, last), count in states.items():
            compact[m, h] += count
        require(actual == compact, f'Original-word and compact marginals disagree at n={n}')
        predicted = defaultdict(Fraction)
        if n == 1:
            predicted[1, 1] = Fraction(1)
        for order in range(1, n):
            derivative = defaultdict(int)
            for (a_exp, b_exp), value in polynomial_history[n - order].items():
                if a_exp >= order:
                    derivative[a_exp - order, b_exp] += (
                        value * factorial(a_exp) // factorial(a_exp - order))
                if b_exp >= order:
                    derivative[a_exp + order, b_exp - order + 1] -= (
                        (-1) ** order * value * factorial(b_exp)
                        // factorial(b_exp - order))
            for power in range(order):
                multiplier = Fraction(comb(order - 1, power)
                    * (-1) ** (order - 1 - power), factorial(order))
                for (a_exp, b_exp), value in derivative.items():
                    predicted[a_exp, b_exp + power] += multiplier * value
        predicted = {key: value for key, value in predicted.items() if value}
        require(predicted == dict(compact), f'Catalytic recurrence disagrees at n={n}')
        polynomial_history.append(compact)
        require(len(words) == archived[n], f'Direct word count disagrees at n={n}')
        following = defaultdict(int)
        for (m, h, last), count in states.items():
            for i in range(m):
                following[m - 1, h + (i >= last), i] += count
            for i in range(m, m + h):
                following[m + 1, h - 1 + (i >= last), i + 1] += count
        states = following
        extensions = []
        for word in words:
            counts = Counter(word)
            ascents = sum(a < b for a, b in zip(word, word[1:]))
            for i in range(ascents + 2):
                if counts[i] < 2:
                    extensions.append(word + (i,))
        words = extensions
    a = numerical_file(HERE / 'normalized_transfer_cut120.txt')
    b = numerical_file(HERE / 'normalized_transfer_cut200.txt')
    for n in range(1, 1201):
        require(a[n][1] == b[n][1], f'Strict-cutoff ratios disagree at n={n}')
    with localcontext() as context:
        context.prec = 70
        errors = []
        for n in range(1, 396):
            exact_ratio = Decimal(archived[n]) / (n * Decimal(archived[n - 1]))
            errors.append((abs(a[n][1] - exact_ratio), n))
        error, index = max(errors)
        require(error < Decimal('2e-17'),
                f'Floating ratio error exceeds tolerance: {error} at n={index}')
    print('All 177 OEIS coefficients agree with archived exact data')
    print('Direct words, compact marginals and exact catalytic recurrence agree through n=9')
    print('Numerical tables have unique indices 1..1200 and finite positive ratios')
    print('Strict-cutoff numerical ratios agree through n=1200')
    print(f'Maximum floating ratio error through 395: {error} at n={index}')

if __name__ == '__main__':
    try:
        main()
    except (VerificationError, OSError) as error:
        print(f'Verification failed: {error}', file=sys.stderr)
        sys.exit(1)
