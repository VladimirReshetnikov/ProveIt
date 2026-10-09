"""Independent verifier. Deliberately imports NONE of the producer modules."""
from __future__ import annotations
from math import comb
from typing import Sequence


def _partition(p: Sequence[int]) -> tuple[int, ...]:
    p = tuple(p)
    if not p:
        raise ValueError("empty interface")
    seen: set[int] = set()
    for a in p:
        if type(a) is not int or a < 0 or (a not in seen and a != len(seen)):
            raise ValueError("noncanonical partition")
        seen.add(a)
    return p


def reference_row(p: Sequence[int]) -> int:
    """Enumerate ALL root sets, rather than products of the blocks."""
    p = _partition(p)
    answer = 0
    for mask in range(1 << (len(p) - 1)):
        counts = [0] * (max(p) + 1)
        counts[p[0]] = 1
        for i in range(1, len(p)):
            if mask >> (i - 1) & 1:
                counts[p[i]] += 1
        if all(x == 1 for x in counts):
            answer |= 1 << mask
    return answer


def graph_completion(p: Sequence[int], q: Sequence[int]) -> bool:
    """Breadth-first graph connectivity and edge count, independent of DSU."""
    p, q = _partition(p), _partition(q)
    if len(p) != len(q):
        raise ValueError("width mismatch")
    a = max(p) + 1
    v = a + max(q) + 1
    if len(p) != v - 1:
        return False
    adj = [set() for _ in range(v)]
    for x, y in zip(p, q):
        adj[x].add(a + y)
        adj[a + y].add(x)
    seen, todo = {0}, [0]
    while todo:
        x = todo.pop()
        for y in adj[x] - seen:
            seen.add(y)
            todo.append(y)
    return len(seen) == v


def verify_certificate(partitions: Sequence[Sequence[int]], costs: Sequence[int],
                       cert: object, *, max_width: int = 16) -> bool:
    """Verify identities and cost dominance against caller-supplied input.

    No digest is trusted instead of the source. False means invalid evidence,
    not a negative conclusion about any surface or knot.
    """
    try:
        if type(max_width) is not int or max_width < 1:
            return False
        if type(cert) is not dict or set(cert) != {"version", "width", "retained", "expansions"}:
            return False
        if type(cert["version"]) is not int or cert["version"] != 1:
            return False
        if type(cert["width"]) is not int:
            return False
        if len(partitions) != len(costs) or any(type(x) is not int for x in costs):
            return False
        if not partitions:
            return cert == {"version": 1, "width": 0, "retained": [], "expansions": []}
        ps = [_partition(x) for x in partitions]
        r = len(ps[0])
        if r > max_width or cert["width"] != r or any(len(x) != r for x in ps):
            return False
        keep, expansions = cert["retained"], cert["expansions"]
        if type(keep) is not list or type(expansions) is not list:
            return False
        if any(type(i) is not int or not 0 <= i < len(ps) for i in keep):
            return False
        if len(set(keep)) != len(keep) or len(keep) > 1 << (r - 1):
            return False
        if len(expansions) != len(ps):
            return False
        for c in range(1, r + 1):
            if sum(max(ps[i]) + 1 == c for i in keep) > comb(r - 1, c - 1):
                return False
        rows = [reference_row(p) for p in ps]
        allowed = set(keep)
        for i, indices in enumerate(expansions):
            if type(indices) is not list:
                return False
            if any(type(j) is not int or j not in allowed for j in indices):
                return False
            if len(indices) != len(set(indices)):
                return False
            row = 0
            for j in indices:
                if costs[j] > costs[i]:
                    return False
                row ^= rows[j]
            if row != rows[i]:
                return False
        return True
    except (ValueError, TypeError, KeyError, IndexError):
        return False
