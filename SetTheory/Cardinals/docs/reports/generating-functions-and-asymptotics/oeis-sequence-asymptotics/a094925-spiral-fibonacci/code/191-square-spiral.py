"""Exact square Spiro-Fibonacci recurrence; all validation survives Python -O.

The model and quarter-square predecessor rule are prior work: see DATA_SOURCES.md.
The coordinate checker generates its path separately and does not call this
module to choose a geometric neighbor.
"""
from math import isqrt

MAX_INDEX = 1000000


def integer(value, minimum, maximum, name):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f'{name} must be an integer in {minimum}..{maximum}')
    return value


def quarter(k):
    integer(k, 0, 2 * MAX_INDEX + 2, 'quarter-square argument')
    return k * k // 4


def predecessor(n):
    """t(0)=t(1)=0 are bookkeeping; the two-term recurrence starts at n=2."""
    integer(n, 0, MAX_INDEX, 'index')
    if n < 2:
        return 0
    k = isqrt(4 * n + 1)
    return n - 2 * k + 3 + int(n == quarter(k))


def predecessors(last):
    integer(last, 0, MAX_INDEX, 'last index')
    return [predecessor(n) for n in range(last + 1)]


def validate_predecessors(rows):
    if type(rows) is not list or not 1 <= len(rows) <= MAX_INDEX + 1:
        raise ValueError('predecessors must be a nonempty bounded list')
    for n, t in enumerate(rows):
        if type(t) is not int or not 0 <= t <= max(0, n - 2):
            raise ValueError('invalid predecessor entry')
        if t != predecessor(n):
            raise ValueError('predecessor disagrees with the square-spiral rule')
    return rows


def values(last):
    """a(0),...,a(last), computed with exact integers and the prescribed seeds."""
    integer(last, 0, MAX_INDEX, 'last index')
    result = [0] if last == 0 else [0, 1]
    for n in range(2, last + 1):
        result.append(result[-1] + result[predecessor(n)])
    return result
