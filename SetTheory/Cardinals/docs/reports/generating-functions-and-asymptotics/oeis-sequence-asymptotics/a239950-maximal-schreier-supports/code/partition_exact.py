#!/usr/bin/env python3
"""Positive integer DP for partitions whose least part is their support size."""
from math import isqrt


def counts(limit):
    if type(limit) is not int or not 0 <= limit <= 1500:
        raise ValueError('limit must be an integer in [0,1500]')
    maximum = (1 + isqrt(1 + 24 * limit)) // 6
    rows = [[0] * (limit + 1) for _ in range(maximum + 1)]
    rows[0][0] = 1
    result = [0] * (limit + 1)
    for minimum in range(limit, 0, -1):
        cap = min(maximum, (1 - 2 * minimum +
                  isqrt((2 * minimum - 1) ** 2 + 8 * limit)) // 2)
        for distinct in range(cap, 0, -1):
            lower = distinct * minimum + distinct * (distinct - 1) // 2
            old, current = rows[distinct - 1], rows[distinct]
            added = [0] * (limit + 1)
            for total in range(lower, limit + 1):
                value = added[total - minimum] + old[total - minimum]
                added[total] = value
                current[total] += value
                if distinct == minimum:
                    result[total] += value
    return result


def partitions(total, minimum=1):
    """Independent unoptimized enumeration, for small finite checks only."""
    if type(total) is not int or type(minimum) is not int or total < 0 or minimum < 1:
        raise ValueError('invalid partition enumeration inputs')
    if total == 0:
        yield ()
    else:
        for part in range(minimum, total + 1):
            for tail in partitions(total - part, part):
                yield (part,) + tail
