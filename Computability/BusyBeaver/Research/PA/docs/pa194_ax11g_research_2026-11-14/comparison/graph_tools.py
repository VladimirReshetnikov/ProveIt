#!/usr/bin/env python3
"""Independent exact full-tuple census of the available 194-control tables.

This is a graph inventory, not a correctness proof. All spanning roots are
considered. The stronger comparison also exchanges symbols, reflects moves,
and ignores the final write/move when entering the unique halt label.
"""
import argparse
import csv
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path


def parse(path):
    table = {}
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, d, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in table
        table[q, b] = (w, int(d == 'R'), target)
    states = set(q for q, b in table)
    assert len(table) == 2 * len(states)
    assert all((q, b) in table for q in states for b in (0, 1))
    halt = set(t for w, d, t in table.values()) - states
    assert len(halt) == 1
    return table, states


def spanning_roots(table, states):
    """The sole source SCC, if any, is exactly the set of spanning roots."""
    adj = {q: [table[q, b][2] for b in (0, 1) if table[q, b][2] in states]
           for q in states}
    reverse = {q: [] for q in states}
    for q, ts in adj.items():
        for t in ts:
            reverse[t].append(q)
    seen, order = set(), []
    def dfs(q):
        if q in seen:
            return
        seen.add(q)
        for t in adj[q]:
            dfs(t)
        order.append(q)
    for q in states:
        dfs(q)
    comp, groups = {}, []
    def back(q, k):
        if q in comp:
            return
        comp[q] = k
        groups[k].append(q)
        for t in reverse[q]:
            back(t, k)
    for q in reversed(order):
        if q not in comp:
            groups.append([])
            back(q, len(groups) - 1)
    incoming = set()
    for q, ts in adj.items():
        for t in ts:
            if comp[q] != comp[t]:
                incoming.add(comp[t])
    sources = set(range(len(groups))) - incoming
    return sorted(groups[sources.pop()]) if len(sources) == 1 else []


def canonical(table, states, *, strong=False):
    roots = spanning_roots(table, states)
    if not roots:
        return None
    best = None
    for flip in ((0, 1) if strong else (0,)):
        for mirror in ((0, 1) if strong else (0,)):
            for start in roots:
                index, order, out = {start: 0}, [start], []
                cmp = 0
                greater = False
                for q in order:
                    for b in (0, 1):
                        w, d, t = table[q, b ^ flip]
                        if t in states:
                            if t not in index:
                                index[t] = len(order)
                                order.append(t)
                            triple = (w ^ flip, d ^ mirror, index[t])
                        else:
                            triple = (0, 0, -1) if strong else (w, d, -1)
                        for item in triple:
                            if best is not None and cmp == 0:
                                old = best[len(out)]
                                cmp = (item > old) - (item < old)
                                if cmp > 0:
                                    greater = True
                                    break
                            out.append(item)
                        if greater:
                            break
                    if greater:
                        break
                if not greater:
                    assert len(order) == len(states)
                    if best is None or tuple(out) < best:
                        best = tuple(out)
    return best


def sha(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()

