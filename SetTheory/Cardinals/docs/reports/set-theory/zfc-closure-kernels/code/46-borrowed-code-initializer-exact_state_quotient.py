"""Exact deterministic transition quotient and an independent row checker.

This is a finite state quotient, not a semantic equivalence oracle for TMs.
Every input tape, head movement, write, and exact halting time is preserved.
"""
from __future__ import annotations


def minimize(table):
    n = len(table)//2
    assert set(table) == {(q, b) for q in range(n) for b in (0, 1)}
    block = [0]*n + [1]
    while True:
        keys = [tuple((w, d, block[t]) for w, d, t in (table[q, 0], table[q, 1]))
                for q in range(n)] + [('HALT',)]
        index = {}
        new = [index.setdefault(key, len(index)) for key in keys]
        if new == block:
            break
        block = new
    m = block[n]
    assert set(block[:n]) == set(range(m))
    quotient = {}
    groups = [[] for _ in range(m)]
    for q in range(n):
        groups[block[q]].append(q)
        for b in (0, 1):
            w, d, t = table[q, b]
            key, value = (block[q], b), (w, d, block[t])
            assert key not in quotient or quotient[key] == value
            quotient[key] = value
    certificate = dict(state_map=block, source_states=n, target_states=m,
                       nontrivial_classes=[g for g in groups if len(g)>1],
                       exact_step_homomorphism=True, kernel_checked=False)
    verify(table, quotient, certificate)
    return quotient, certificate


def verify(source, target, certificate):
    n, m = len(source)//2, len(target)//2
    h = certificate['state_map']
    assert set(source) == {(q, b) for q in range(n) for b in (0, 1)}
    assert set(target) == {(q, b) for q in range(m) for b in (0, 1)}
    assert len(h) == n+1 and h[n] == m and h[0] == 0
    assert set(h[:n]) == set(range(m))
    for (q, b), (write, direction, next_state) in source.items():
        assert 0 <= next_state <= n
        assert target[h[q], b] == (write, direction, h[next_state])
    return True


def encode(table):
    lines = ['#! start 0']
    for (q, b), (w, d, t) in sorted(table.items()):
        lines.append(f'{q} {b} {w} {d} {t}')
    return ('\n'.join(lines)+'\n').encode()


def parse(data):
    rows = {}
    for line in data.decode().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, d, t = line.split()
        key = int(q), int(b)
        assert key not in rows and d in ('L', 'R') and int(w) in (0, 1)
        rows[key] = int(w), d, int(t)
    return rows
