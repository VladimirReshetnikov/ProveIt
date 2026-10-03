"""Closed-form observations, using only integer arithmetic."""
from math import isqrt


def _validate(k, n):
    if type(k) is not int or k < 7 or type(n) is not int or n < 0:
        raise ValueError("Expected integer k >= 7 and a nonnegative integer")


def section_time(k, n):
    _validate(k, n)
    return n*n + (2*k - 11)*n


def visited(k, x, y):
    _validate(k, 0)
    return y >= 0 and (x == 0 or 2 <= x <= k+y-2 or x == k+y)


def first_arrival(k, x, y):
    if not visited(k, x, y):
        return None
    n, d = y, k+y
    t = section_time(k, n)
    if x in (0, 3, 4):
        return t
    if x == 2:
        return t + 2*d - 11
    if x == d:
        return 0 if n == 0 else t - (d - 6)
    return t + x - 4


def centered_count(k, radius):
    _validate(k, radius)
    n = radius
    if n == 0:
        return 1
    if n <= k-2:
        return n*(n+1)
    return (n*n + (2*k-1)*n - k*k + 3*k - 4)//2


def quadratic_count(bound, linear, constant, first):
    """Count n>=first with n²+linear*n+constant <= bound, linear>=0."""
    if first < 0 or linear < 0:
        raise ValueError("Expected nonnegative lower limit and linear term")
    discriminant = linear*linear + 4*(bound - constant)
    if discriminant < 0:
        return 0
    last = (isqrt(discriminant)-linear)//2
    return max(0, last-first+1)


def drift_count(k, radius):
    _validate(k, radius)
    if radius < k+1:
        raise ValueError("This formula requires radius >= k+1")
    a = quadratic_count(radius, 2*k-10, -1, 1)
    b = quadratic_count(radius, 2*k-9, k-5, 0)
    return 4*(radius+1) - 3*a - b
