"""Certificates for the nice-order hypothesis; cubic-time greedy construction.

No claim of optimal girth is made. A failed certificate removes the complexity
promise, not the correctness of an extremal-window computation.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass

class OrderError(ValueError):
    pass

@dataclass(frozen=True)
class OrderCertificate:
    order: tuple[int, ...]
    nice: bool
    girth: int
    attachments: tuple[int, ...]
    reason: str

def graph(pd):
    where = defaultdict(list)
    for v, row in enumerate(pd):
        for e in row:
            where[e].append(v)
    if any(len(v) != 2 for v in where.values()):
        raise OrderError('invalid PD edge multiplicities')
    adj = [set() for _ in pd]
    for u, v in where.values():
        adj[u].add(v); adj[v].add(u)
    return dict(where), adj

def connected(vertices, adj):
    if not vertices:
        return True
    seen, stack = set(), [min(vertices)]
    while stack:
        u = stack.pop()
        if u in seen:
            continue
        seen.add(u)
        stack.extend((adj[u] & vertices) - seen)
    return seen == vertices

def certify(pd, order):
    n = len(pd)
    order = tuple(order)
    if len(order) != n or set(order) != set(range(n)):
        raise OrderError('order must permute the crossings')
    where, adj = graph(pd)
    boundary, girth, attachments, prior = set(), 0, [], set()
    reason = ''
    if n < 2:
        reason = 'fewer than two crossings; use trivial-case handling'
    if any(u == v for u, v in where.values()):
        reason = 'projection contains a loop edge'
    remaining = set(range(n))
    for t, v in enumerate(order):
        flags = [e in boundary for e in pd[v]]
        a = sum(flags)
        attachments.append(a)
        if 0 < t < n - 1:
            transitions = sum(flags[j] != flags[(j + 1) % 4] for j in range(4))
            if not 1 <= a <= 3 or transitions != 2:
                reason = reason or 'nonconsecutive or empty interior attachment'
        if t == n - 1 and n >= 2 and a != 4:
            reason = reason or 'last crossing is not the sole four-edge closure'
        for e in pd[v]:
            if e in boundary:
                boundary.remove(e)
            else:
                boundary.add(e)
        prior.add(v); remaining.remove(v)
        if not connected(prior, adj) or not connected(remaining, adj):
            reason = reason or 'disconnected prefix or suffix'
        girth = max(girth, len(boundary))
    return OrderCertificate(order, not reason, girth, tuple(attachments), reason)

def nice_order(pd):
    n = len(pd)
    if n < 2:
        return certify(pd, range(n))
    where, adj = graph(pd)
    vertices = set(range(n))
    if any(u == v for u, v in where.values()) or not connected(vertices, adj):
        raise OrderError('requires a loopless connected projection')
    if any(not connected(vertices - {v}, adj) for v in vertices):
        raise OrderError('projection is not two-connected')
    order, prefix, remaining = [0], {0}, vertices - {0}
    while remaining:
        candidates = [v for v in remaining if adj[v] & prefix and connected(remaining - {v}, adj)]
        if not candidates:
            raise OrderError('no connected-prefix/suffix extension found')
        def cost(v):
            p = prefix | {v}
            cut = sum((u in p) != (w in p) for u, w in where.values())
            return cut, v
        v = min(candidates, key=cost)
        order.append(v); prefix.add(v); remaining.remove(v)
    cert = certify(pd, order)
    if not cert.nice:
        raise OrderError(cert.reason)
    return cert
