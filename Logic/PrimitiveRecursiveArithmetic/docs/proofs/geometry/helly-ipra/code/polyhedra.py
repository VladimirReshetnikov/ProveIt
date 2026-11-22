"""Exact Helly alternative for grouped rational linear inequalities.

A row (a, b) means a dot x <= b. Coordinates and constants may be
integers or fractions.Fraction objects. No external libraries are used.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations


def _rational(x):
    if not isinstance(x, (int, Fraction)):
        raise TypeError("expected an integer or Fraction")
    return Fraction(x)


def _rows(d, rows):
    if type(d) is not int or d < 0:
        raise ValueError("dimension must be a nonnegative integer")
    result = []
    for a, b in rows:
        if len(a) != d:
            raise ValueError("row dimension mismatch")
        result.append((tuple(map(_rational, a)), _rational(b)))
    return result


def satisfies(point, rows):
    for a, b in rows:
        if len(a) != len(point):
            raise ValueError("dimension mismatch")
        if sum(x * c for x, c in zip(point, a)) > b:
            return False
    return True


def solve(d, rows):
    """Return a rational feasible point, or None for an infeasible system."""
    current = _rows(d, rows)
    history = []
    for _ in range(d):
        lower, upper, projected = [], [], []
        for a, b in current:
            p = a[-1]
            if p > 0:
                upper.append((a[:-1], p, b))
            elif p < 0:
                lower.append((a[:-1], p, b))
            else:
                projected.append((a[:-1], b))
        for la, lp, lb in lower:
            for ua, up, ub in upper:
                left = tuple(up * x - lp * y for x, y in zip(la, ua))
                projected.append((left, up * lb - lp * ub))
        history.append((lower, upper))
        current = projected
    if any(b < 0 for _, b in current):
        return None

    point = ()
    for lower, upper in reversed(history):
        def endpoint(row):
            a, p, b = row
            return (b - sum(x * c for x, c in zip(point, a))) / p
        if lower:
            value = max(map(endpoint, lower))
        elif upper:
            value = min(map(endpoint, upper))
        else:
            value = Fraction(0)
        point += (value,)
    return point


@dataclass
class Feasible:
    point: tuple


@dataclass
class Infeasible:
    indices: tuple


def decide_family(d, family):
    """Return Feasible(point) or Infeasible(a small tuple of group indices)."""
    from helly import helly
    groups = [_rows(d, group) for group in family]
    if not groups:
        if type(d) is not int or d < 0:
            raise ValueError("dimension must be a nonnegative integer")
        return Feasible((Fraction(0),) * d)
    n = len(groups)
    local = {}
    for subset in combinations(range(n), min(d + 1, n)):
        x = solve(d, [row for i in subset for row in groups[i]])
        if x is None:
            return Infeasible(subset)
        local[subset] = x
    certificate = helly(d, n, local)
    return Feasible(certificate.point)
