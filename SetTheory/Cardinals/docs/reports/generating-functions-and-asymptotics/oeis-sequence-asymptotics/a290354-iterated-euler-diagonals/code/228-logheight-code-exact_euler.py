#!/usr/bin/env python3
"""Finite exact Euler transforms; adapted from the Report226 public recurrence.

F_0(z)=z; F_(m+1)(z)=prod_(d>=1)(1-z**d)**(-[z**d]F_m)-1.
Every supported degree AND height is an integer in [0,640].  This is a
finite-computation resource cap, not a bound supplied by an asymptotic theorem.
"""
from math import comb

MAX_INDEX = 640
MAX_PRODUCT_DEGREE = 20


def bounded_index(value):
    if isinstance(value, bool) or not isinstance(value, int) or not 0 <= value <= MAX_INDEX:
        raise ValueError('degree/height must be an integer from 0 to 640')
    return value


def decimal_integer(value):
    """Render any integer in base 10 without changing CPython's digit limit."""
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError('integer required')
    if value == 0:
        return '0'
    sign = '-' if value < 0 else ''
    value = abs(value)
    chunks = []
    while value:
        value, part = divmod(value, 10**9)
        chunks.append(part)
    return sign + str(chunks[-1]) + ''.join(f'{part:09d}' for part in reversed(chunks[:-1]))


def validate_row(row):
    if not isinstance(row, list) or not row:
        raise ValueError('nonempty coefficient list required')
    bounded_index(len(row)-1)
    if row[0] != 0 or any(isinstance(v, bool) or not isinstance(v, int) or v < 0 for v in row):
        raise ValueError('F row must have constant zero and nonnegative integer entries')


def euler_step(row):
    """Exact recurrence: b_k=sum_(d|k)d*a_d; k*c_k=sum_(j=1)^k b_j*c_(k-j)."""
    validate_row(row)
    degree = len(row)-1
    divisor = [0]*(degree+1)
    for d in range(1, degree+1):
        weight = d*row[d]
        for k in range(d, degree+1, d):
            divisor[k] += weight
    nxt = [1]+[0]*degree
    for k in range(1, degree+1):
        numerator = sum(divisor[j]*nxt[k-j] for j in range(1, k+1))
        nxt[k], remainder = divmod(numerator, k)
        if remainder:
            raise ArithmeticError('Euler-transform division is not integral')
    nxt[0] = 0
    return nxt


def product_step(row):
    """Independent finite-product implementation, capped at degree 20."""
    validate_row(row)
    degree = len(row)-1
    if degree > MAX_PRODUCT_DEGREE:
        raise ValueError('independent product implementation is capped at degree 20')
    result = [1]+[0]*degree
    for d in range(1, degree+1):
        exponent = row[d]
        if not exponent:
            continue
        factor = [comb(exponent+k-1, k) for k in range(degree//d+1)]
        out = [0]*(degree+1)
        for a, value in enumerate(result):
            for k in range((degree-a)//d+1):
                out[a+k*d] += value*factor[k]
        result = out
    result[0] = 0
    return result


def coefficients(degree, height):
    bounded_index(degree)
    bounded_index(height)
    row = [0]*(degree+1)
    if degree:
        row[1] = 1
    for _ in range(height):
        row = euler_step(row)
    return row


def exact_targets(degree, heights):
    """Return A(degree,m) for requested heights using one iteration per degree.

    A(0,m)=1 is the separate array convention, not the constant term of F_m.
    """
    bounded_index(degree)
    if not isinstance(heights, (list, tuple)) or not heights:
        raise ValueError('nonempty list or tuple of heights required')
    for height in heights:
        bounded_index(height)
    targets = set(heights)
    row = [0]*(degree+1)
    if degree:
        row[1] = 1
    out = {}
    if 0 in targets:
        out[0] = row[degree] if degree else 1
    for height in range(1, max(targets)+1):
        row = euler_step(row)
        if height in targets:
            out[height] = row[degree] if degree else 1
    return out


def euler_zigzag(index):
    """E_index from (sec z+tan z)'=((sec z+tan z)**2+1)/2."""
    bounded_index(index)
    if index == 0:
        return 1
    values = [1, 1]
    for n in range(1, index):
        numerator = sum(comb(n, k)*values[k]*values[n-k] for k in range(n+1))
        quotient, remainder = divmod(numerator, 2)
        if remainder:
            raise ArithmeticError('Euler-zigzag division is not integral')
        values.append(quotient)
    return values[index]
