#!/usr/bin/env python3
"""Standalone exhaustive degree <= 9 certificate; Python standard library."""
from itertools import product


def partitions(s, low=1):
    if s == 0:
        yield ()
    for u in range(low, s + 1):
        for tail in partitions(s - u, u):
            yield (u,) + tail


def unimodal(c):
    falling = False
    for x, y in zip(c, c[1:]):
        if y < x:
            falling = True
        if falling and y > x:
            return False
    return True


counts, failures = [], []
for degree in range(1, 10):
    count = 0
    for r in range(2, degree):
        for b in range(2, 2 + (degree - 1) // r):
            s = degree - r * (b - 1)
            for p in partitions(s):
                a = tuple(u + 1 for u in p)
                c = [0] * (degree + 1)
                for v in product(*(range(u) for u in a), range(b)):
                    c[sum(v[:-1]) + r * v[-1]] += 1
                condition = (any(u % r == 0 for u in a)
                             or b <= 1 + sum(u // r for u in a))
                applies = len(a) <= 3 or r <= 3
                if applies and unimodal(c) and not condition:
                    failures.append((degree, r, b, a))
                count += 1
    counts.append(count)
expected = [(9, 3, 2, (2, 2, 2, 2, 2, 2))]
if counts != [0, 0, 1, 3, 7, 13, 23, 38, 59]:
    raise RuntimeError(("case counts", counts))
if failures != expected:
    raise RuntimeError(("counterexamples", failures))
print("PASS:", sum(counts), "normalized cases")
print("Counts by degree:", counts)
print("Counterexamples:", failures)
