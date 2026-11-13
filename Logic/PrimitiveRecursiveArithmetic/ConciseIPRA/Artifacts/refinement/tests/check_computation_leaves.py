"""Finite semantic search for the two-field direct computation recognizer.

This supports the paper proof, not a substitute for it. Integer/list inputs
only, fixed rigid parameter assignment, and a bounded evaluation budget.
"""
import json
import random

FLOOR = -1
MISSING = object()

def opening(a, t=MISSING, d=0):
    if isinstance(a, list):
        return [opening(b, t, d + 5 - len(a)) for b in a]
    if FLOOR <= a < d:
        return a
    return d % 2 and opening(t, d=3)

def compute_leaf(a):
    opening(a)
    b, r = a
    n, b, h = b
    if n:
        n, = n
        b = opening(h, [n, b, h], 3)
    return b == r

def value(a, env=(), budget=None):
    if budget is None:
        budget = [1000]
    budget[0] -= 1
    if budget[0] < 0:
        raise RuntimeError('budget')
    if type(a) is int:
        if a < 0:
            return 2
        if a < 3:
            return 0
        return env[(a - 3) // 2]
    if len(a) == 1:
        return 1 + value(a[0], (0, 0) + env, budget)
    if len(a) == 3:
        n = value(a[0], (0,) + env, budget)
        u = value(a[1], (0,) + env, budget)
        if n > 20:
            raise RuntimeError('counter')
        for _ in range(n):
            u = value(a[2], (u,) + env, budget)
        return u
    return 0

def term(depth):
    if depth == 0 or random.randrange(3) == 0:
        return random.choice([-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    n = random.choice([0, 1, 1, 2, 3, 3, 4, 5, 6])
    return [term(depth - 1) for _ in range(n)]

def main():
    random.seed(73261)
    counts = dict(attempted=0, scope_rejected=0, accepted=0,
                  evaluated=0, evaluation_limited=0, false_equalities=0)
    for _ in range(20000):
        counts['attempted'] += 1
        n, b, h = term(3), term(3), term(3)
        try:
            if random.randrange(2):
                a = [[[n], b, h], opening(h, [n, b, h], 3)]
            else:
                a = [[random.choice([0, []]), b, h], b]
            if not compute_leaf(a):
                continue
        except (TypeError, ValueError, RecursionError):
            counts['scope_rejected'] += 1
            continue
        counts['accepted'] += 1
        try:
            left, right = value(a[0]), value(a[1])
        except RuntimeError:
            counts['evaluation_limited'] += 1
            continue
        except IndexError as err:
            raise AssertionError(('accepted escaping slot', a)) from err
        counts['evaluated'] += 1
        if left != right:
            counts['false_equalities'] += 1
            raise AssertionError((a, left, right))
    print(json.dumps(counts, indent=2))

if __name__ == '__main__':
    main()
