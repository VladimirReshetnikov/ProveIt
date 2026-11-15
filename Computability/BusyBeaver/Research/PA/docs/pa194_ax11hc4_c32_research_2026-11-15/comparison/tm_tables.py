#!/usr/bin/env python3
"""Strict five-column binary TM tables and exact rooted graph forms."""
import re

def parse(data):
    rows, declared = {}, None
    for line in data.decode('ascii').splitlines():
        if not line.strip():
            continue
        if line.lstrip().startswith('#'):
            m = re.search(r'\bstart\s*(\d+)', line)
            if m and declared is None:
                declared = int(m.group(1))
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        if b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R') or (q, b) in rows:
            raise ValueError('invalid transition: ' + line)
        rows[q, b] = (w, d, n)
    states = {q for q, b in rows}
    if not states or any((q, b) not in rows for q in states for b in (0, 1)):
        raise ValueError('incomplete binary table')
    start = declared if declared is not None else 0 if sorted(states) == list(range(len(states))) else None
    if start is not None and start not in states:
        raise ValueError('start lacks transitions')
    return rows, states, start, declared is not None

def canonical(rows, states, start, mirror=False, flip=False, loose=True):
    index, order, out = {start: 0}, [start], []
    for q in order:
        for b in (0, 1):
            w, d, n = rows[q, b ^ int(flip)]
            if n not in states:
                out.append((0, 'R', -1) if loose else (w ^ int(flip), ('L' if d == 'R' else 'R') if mirror else d, -1))
                continue
            if n not in index:
                index[n] = len(index)
                order.append(n)
            out.append((w ^ int(flip), ('L' if d == 'R' else 'R') if mirror else d, index[n]))
    return tuple(out), len(order)

def compare_root(rows, states, root, expected):
    index, order, k = {root: 0}, [root], 0
    for q in order:
        for b in (0, 1):
            w, d, n = rows[q, b]
            if n not in states:
                triple = (0, 'R', -1)
            else:
                if n not in index:
                    index[n] = len(index)
                    order.append(n)
                triple = (w, d, index[n])
            if k == len(expected) or triple != expected[k]:
                return False, k
            k += 1
    return k == len(expected), k

def has_spanning_root(rows, states):
    for root in states:
        seen, todo = {root}, [root]
        for q in todo:
            for b in (0, 1):
                n = rows[q, b][2]
                if n in states and n not in seen:
                    seen.add(n)
                    todo.append(n)
        if len(seen) == len(states):
            return True
    return False
