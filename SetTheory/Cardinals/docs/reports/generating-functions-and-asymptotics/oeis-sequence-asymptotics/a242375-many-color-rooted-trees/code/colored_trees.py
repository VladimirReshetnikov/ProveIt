#!/usr/bin/env python3
"""Exact counts for Report 222. Python 3.10+, standard library only.

All interfaces are bounded deliberately. No process-global integer conversion,
precision, or recursion setting is changed. Decimal chunking is for computed
integer outputs only; user threshold input remains limited to 600 digits.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
import sys

MAX_N = 2000
MAX_Q = 1_000_000
MAX_THRESHOLD_DIGITS = 600
KINDS = ('all', 'identity', 'zero', 'B')


def integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer in [{low}, {high}]')
    return value


def parse_small(text):
    if not isinstance(text, str) or not text.isascii() or not text.isdecimal() or len(text) > 10:
        raise argparse.ArgumentTypeError('expected at most 10 ASCII decimal digits')
    return int(text)


def parse_target(text):
    if not isinstance(text, str) or not text.isascii() or not text.isdecimal() or not 1 <= len(text) <= MAX_THRESHOLD_DIGITS:
        raise ValueError('target must contain 1 to 600 ASCII decimal digits')
    # Below Python's smallest configurable limit of 640; never disable the guard.
    result = int(text)
    if result < 1:
        raise ValueError('target must be positive')
    return result


def decimal(value):
    """Serialize a trusted computed integer without altering Python's guards."""
    if type(value) is not int:
        raise TypeError('computed integer required')
    if value == 0:
        return '0'
    sign = '-' if value < 0 else ''
    value = abs(value)
    pieces = []
    while value:
        value, part = divmod(value, 1_000_000_000)
        pieces.append(part)
    return sign + str(pieces[-1]) + ''.join(f'{p:09d}' for p in reversed(pieces[:-1]))


def divisors(n):
    result = [[] for _ in range(n + 1)]
    for d in range(1, n + 1):
        for m in range(d, n + 1, d):
            result[m].append(d)
    return result


def counts(N, q, kind='all'):
    """A[0]=0, A[1]=1; N is TOTAL vertices. q is positive integer."""
    integer(N, 'N', 1, MAX_N)
    integer(q, 'q', 1, MAX_Q)
    if kind not in KINDS:
        raise ValueError('kind must be all, identity, zero, or B')
    ds = divisors(N - 1)
    A = [0, 1] + [0] * (N - 1)
    b = [0] * N
    signed = kind in ('identity', 'B')
    for n in range(2, N + 1):
        m = n - 1
        b[m] = sum(d * A[d] * (-1 if signed and m // d % 2 == 0 else 1) for d in ds[m])
        if kind == 'zero' and m % 2 == 0:
            b[m] -= 2
        if kind == 'B':
            b[m] += (2 if m % 2 == 0 else 0) - (3 if m % 3 == 0 else 0)
        numerator = q * sum(A[n - j] * b[j] for j in range(1, n))
        value, rem = divmod(numerator, n - 1)
        if rem or value < 0:
            raise ArithmeticError('nonintegral or negative coefficient')
        A[n] = value
    return A


def diagonal(n, kind='all'):
    integer(n, 'n', 0, MAX_N - 1)
    if kind not in ('all', 'identity'):
        raise ValueError('diagonal kind must be all or identity')
    return 1 if n == 0 else counts(n + 1, n, kind)[-1]


def diagonal_threshold(y, max_n=100, kind='all'):
    """Exact least 0<=n<=max_n with b(n)>=y, or None if absent.

    Monotonicity is combinatorially proved, so binary search is exact. This
    performs no floating-point/asymptotic ceiling operation.
    """
    if type(y) is not int or y < 1:
        raise ValueError('y must be a positive integer')
    integer(max_n, 'max_n', 0, MAX_N - 1)
    if kind not in ('all', 'identity'):
        raise ValueError('diagonal kind must be all or identity')
    if diagonal(max_n, kind) < y:
        return None
    lo, hi = 0, max_n
    while lo < hi:
        mid = (lo + hi) // 2
        if diagonal(mid, kind) >= y:
            hi = mid
        else:
            lo = mid + 1
    return lo


def palette_threshold(N, numerator, denominator, max_q=100):
    """Exact global first palette within 1..max_q, by exhaustive scan.

    Finite-N monotonicity is NOT assumed. Resource bound is N*max_q<=20000.
    """
    integer(N, 'N', 1, MAX_N)
    integer(numerator, 'numerator', 1, 1_000_000_000)
    integer(denominator, 'denominator', 1, 1_000_000_000)
    integer(max_q, 'max_q', 1, MAX_Q)
    if numerator >= denominator:
        raise ValueError('target fraction must lie strictly between zero and one')
    if N * max_q > 20000:
        raise ValueError('palette scan requires N*max_q <= 20000')
    for q in range(1, max_q + 1):
        plus, minus = counts(N, q)[-1], counts(N, q, 'identity')[-1]
        if denominator * minus >= numerator * plus:
            return q
    return None


# Sparse polynomial operations for exact full marked-polynomial verification.
def padd(a, b):
    c = dict(a)
    for k, v in b.items():
        c[k] = c.get(k, 0) + v
        if c[k] == 0:
            del c[k]
    return c


def pscale(a, s):
    return {k: s * v for k, v in a.items() if s * v}


def pmul(a, b):
    c = {}
    for i, x in a.items():
        for j, y in b.items():
            c[i + j] = c.get(i + j, 0) + x * y
    return {k: v for k, v in c.items() if v}


def marked_counts(N, q, kind='all'):
    """Entire polynomials in t as {exponent: integer}; N<=12, q<=100."""
    integer(N, 'N', 1, 12)
    integer(q, 'q', 1, 100)
    if kind not in ('all', 'B'):
        raise ValueError('marked kind must be all or B')
    signed = kind == 'B'
    # Leaf-series L_m and m[x^m]log L are polynomials with integer coefficients.
    leaf = [{m * (m - 1) // 2: 1} if not signed or m <= 2 else {} for m in range(N)]
    logder = [{} for _ in range(N)]
    correction = [{} for _ in range(N)]
    for m in range(1, N):
        value = pscale(leaf[m], m)
        for k in range(1, m):
            value = padd(value, pscale(pmul(logder[k], leaf[m - k]), -1))
        logder[m] = value
        correction[m] = padd(value, {0: -((-1) ** (m - 1) if signed else 1)})
    A, b = [{}, {0: 1}] + [{} for _ in range(N - 1)], [{} for _ in range(N)]
    ds = divisors(N - 1)
    for n in range(2, N + 1):
        m = n - 1
        value = correction[m]
        for d in ds[m]:
            j = m // d
            value = padd(value, pscale({j * k: v for k, v in A[d].items()}, d * ((-1) ** (j - 1) if signed else 1)))
        b[m] = pscale(value, q)
        value = {}
        for j in range(1, n):
            value = padd(value, pmul(A[n - j], b[j]))
        A[n] = {}
        for k, v in value.items():
            coefficient, rem = divmod(v, n - 1)
            if rem or coefficient < 0:
                raise ArithmeticError('invalid marked coefficient')
            if coefficient:
                A[n][k] = coefficient
    return A


def marked_prefix(N, q, K=16):
    """Exact [t^0,...,t^K] of all-class counts and exact unmarked total.

    Marking truncation is exact because all marking exponents are nonnegative.
    Resource guards: N<=640, K<=32 and N*(K+1)<=12000.
    """
    integer(N, 'N', 1, 640)
    integer(q, 'q', 1, MAX_Q)
    integer(K, 'K', 0, 32)
    if N * (K + 1) > 12000:
        raise ValueError('marked prefix requires N*(K+1) <= 12000')
    A = [[0] * (K + 1) for _ in range(N + 1)]
    A[1][0] = 1
    logder = [[0] * (K + 1) for _ in range(N)]
    b = [[0] * (K + 1) for _ in range(N)]
    ds = divisors(N - 1)
    for n in range(2, N + 1):
        m = n - 1
        tri = m * (m - 1) // 2
        if tri <= K:
            logder[m][tri] = m
        for j in range(1, m):
            shift = (m-j) * (m-j-1) // 2
            if shift <= K:
                for k in range(K + 1 - shift):
                    logder[m][k + shift] -= logder[j][k]
        b[m] = logder[m].copy()
        b[m][0] -= 1
        for d in ds[m]:
            dilation = m // d
            for k in range(K // dilation + 1):
                b[m][k * dilation] += d * A[d][k]
        numerator = [0] * (K + 1)
        for j in range(1, n):
            for k, x in enumerate(b[j]):
                if x:
                    for l in range(K + 1 - k):
                        numerator[k + l] += x * A[n-j][l]
        for k, x in enumerate(numerator):
            A[n][k], rem = divmod(q * x, m)
            if rem or A[n][k] < 0:
                raise ArithmeticError('invalid truncated marked coefficient')
    total = counts(N, q)[-1]
    if sum(A[N]) > total:
        raise ArithmeticError('marked prefix exceeds total')
    return A[N], total


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('count')
    p.add_argument('N', type=parse_small); p.add_argument('q', type=parse_small)
    p.add_argument('--kind', choices=KINDS, default='all')
    p = sub.add_parser('diagonal')
    p.add_argument('n', type=parse_small); p.add_argument('--kind', choices=('all', 'identity'), default='all')
    p = sub.add_parser('inverse')
    p.add_argument('target'); p.add_argument('--max-n', type=parse_small, default=100)
    p.add_argument('--kind', choices=('all', 'identity'), default='all')
    p = sub.add_parser('palette')
    p.add_argument('N', type=parse_small); p.add_argument('numerator', type=parse_small); p.add_argument('denominator', type=parse_small)
    p.add_argument('--max-q', type=parse_small, default=100)
    p = sub.add_parser('marked')
    p.add_argument('N', type=parse_small); p.add_argument('q', type=parse_small)
    p.add_argument('--kind', choices=('all', 'B'), default='all')
    args = parser.parse_args(argv)
    try:
        if args.command == 'count':
            print(decimal(counts(args.N, args.q, args.kind)[-1]))
        elif args.command == 'diagonal':
            print(decimal(diagonal(args.n, args.kind)))
        elif args.command == 'inverse':
            answer = diagonal_threshold(parse_target(args.target), args.max_n, args.kind)
            print(json.dumps({'least_index': answer, 'searched_through': args.max_n}))
        elif args.command == 'palette':
            answer = palette_threshold(args.N, args.numerator, args.denominator, args.max_q)
            print(json.dumps({'least_palette': answer, 'searched_through': args.max_q}))
        else:
            print(json.dumps({str(k): decimal(v) for k, v in sorted(marked_counts(args.N, args.q, args.kind)[-1].items())}, sort_keys=True))
    except (ValueError, ArithmeticError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    main()
