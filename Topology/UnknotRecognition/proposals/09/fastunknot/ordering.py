"""The baseline's greedy scan policy, implemented with local heap updates.

At most four unprocessed neighbours change priority when a crossing is added.
For a fixed number of starts this costs O(n log n), rather than O(n**2).
"""
from collections import defaultdict
from heapq import heappop, heappush


def scan_order(pd, start=None):
    n = len(pd)
    if not n:
        return []
    start = 0 if start is None else start
    if type(start) is not int or not 0 <= start < n:
        raise ValueError("invalid starting crossing")
    occurrences = defaultdict(list)
    loops = [4 - len(set(row)) for row in pd]
    neighbours = [[] for _ in pd]
    for i, row in enumerate(pd):
        for e in row:
            occurrences[e].append(i)
    for vertices in occurrences.values():
        if len(vertices) != 2:
            raise ValueError("each edge must occur exactly twice")
        a, b = vertices
        if a != b:
            neighbours[a].append(b)
            neighbours[b].append(a)
    shared = [0] * n
    used = [False] * n
    heap = []

    def push(i):
        heappush(heap, (-shared[i], -2 * loops[i] - 2 * shared[i], i))

    for i in range(n):
        push(i)
    result = []
    current = start
    while len(result) < n:
        if result:
            while True:
                neg_shared, _, current = heappop(heap)
                if not used[current] and neg_shared == -shared[current]:
                    break
        used[current] = True
        result.append(current)
        for other in neighbours[current]:
            if not used[other]:
                shared[other] += 1
                push(other)
    return result


def order_profile(pd, order):
    boundary = set()
    worst = total = 0
    for i in order:
        for e in pd[i]:
            if e in boundary:
                boundary.remove(e)
            else:
                boundary.add(e)
        worst = max(worst, len(boundary))
        total += len(boundary)
    return worst, total


def best_scan_order(pd, tries=None):
    n = len(pd)
    if not n:
        return []
    if tries is not None and (type(tries) is not int or tries <= 0):
        raise ValueError("tries must be positive")
    starts = range(n) if tries is None or tries >= n else range(0, n, max(1, n // tries))
    best = None
    profile = None
    for start in starts:
        candidate = scan_order(pd, start)
        score = order_profile(pd, candidate)
        if profile is None or score < profile:
            best, profile = candidate, score
    return best


def validate_order(order, n):
    result = list(order)
    if len(result) != n or any(type(x) is not int for x in result) or set(result) != set(range(n)):
        raise ValueError("order must be a permutation of all crossing indices")
    return result
