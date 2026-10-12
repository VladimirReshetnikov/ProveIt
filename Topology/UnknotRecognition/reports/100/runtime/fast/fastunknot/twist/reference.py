"""Small, independently assembled crossing-cube reference over F_2.

No twist formulas, no imports from core.py, graph traversal rather than the
macro backend's union-find, and set-based rather than bitset elimination.
This is deliberately slow and restricted to small validation instances.
"""
from __future__ import annotations
from collections import defaultdict
from itertools import product


def cube_homology(strands: int, word: list[int], *, max_crossings: int = 16,
                  check_d2: bool = True) -> dict:
    if type(strands) is not int or strands < 1:
        raise ValueError('invalid strand count')
    if any(type(x) is not int or not 0 < abs(x) < strands for x in word):
        raise ValueError('invalid word')
    n = len(word)
    if n > max_crossings:
        raise ValueError('reference crossing limit exceeded')
    neg = sum(x < 0 for x in word)
    vertices = (n + 1) * strands
    circles = {}
    basis = {}
    dims = defaultdict(int)
    owner = {}
    for state in range(1 << n):
        adj = [set() for _ in range(vertices)]

        def edge(a, b):
            adj[a].add(b)
            adj[b].add(a)

        for j in range(strands):
            edge(j, n * strands + j)
        for k, letter in enumerate(word):
            e = bool((state >> k) & 1) == (letter > 0)
            i = abs(letter) - 1
            for j in range(strands):
                if not e or j not in (i, i + 1):
                    edge(k * strands + j, (k + 1) * strands + j)
            if e:
                edge(k * strands + i, k * strands + i + 1)
                edge((k + 1) * strands + i, (k + 1) * strands + i + 1)
        visited = set()
        groups = []
        for v in range(vertices):
            if v in visited:
                continue
            stack, group = [v], set()
            visited.add(v)
            while stack:
                w = stack.pop()
                group.add(w)
                for q in adj[w]:
                    if q not in visited:
                        visited.add(q)
                        stack.append(q)
            groups.append(frozenset(group))
        circles[state] = groups
        owner[state] = {v: j for j, group in enumerate(groups) for v in group}
        h = state.bit_count() - neg
        for labels in product((0, 1), repeat=len(groups) - 1):
            label = (1,) + labels  # marked component X
            basis[(state, label)] = (h, dims[h])
            dims[h] += 1
    columns = {h: [set() for _ in range(d)] for h, d in dims.items()}
    nnz = 0
    for (state, label), (h, index) in basis.items():
        for k in range(n):
            if state & (1 << k):
                continue
            target = state | (1 << k)
            src, dst = circles[state], circles[target]
            old_to_new = [{owner[target][v] for v in group} for group in src]
            outputs = []
            if len(src) == len(dst) + 1:
                # Label on a merged circle is the sum of exponents; X^2=0.
                target_label = [0] * len(dst)
                for j, image in enumerate(old_to_new):
                    assert len(image) == 1
                    target_label[next(iter(image))] += label[j]
                if max(target_label) < 2:
                    outputs.append(tuple(target_label))
            elif len(src) + 1 == len(dst):
                j = next(j for j, image in enumerate(old_to_new) if len(image) == 2)
                a, b = tuple(old_to_new[j])
                partial = [0] * len(dst)
                for i, image in enumerate(old_to_new):
                    if i != j:
                        partial[next(iter(image))] = label[i]
                for aa, bb in (((1, 1),) if label[j] else ((1, 0), (0, 1))):
                    out = partial.copy()
                    out[a], out[b] = aa, bb
                    outputs.append(tuple(out))
            else:
                raise AssertionError('invalid saddle')
            for out in outputs:
                hh, ii = basis[(target, out)]
                assert hh == h + 1
                if ii in columns[h][index]:
                    columns[h][index].remove(ii)
                else:
                    columns[h][index].add(ii)
                nnz += 1
    if check_d2:
        for h, cols in columns.items():
            for col in cols:
                image = set()
                for j in col:
                    image.symmetric_difference_update(columns[h + 1][j])
                assert not image, 'reference d^2 != 0'
    ranks = {}
    for h, cols in columns.items():
        pivots = {}
        for col in cols:
            col = set(col)
            while col:
                p = max(col)
                if p not in pivots:
                    pivots[p] = col
                    break
                col.symmetric_difference_update(pivots[p])
        ranks[h] = len(pivots)
    by_degree = {h: d - ranks.get(h - 1, 0) - ranks[h] for h, d in sorted(dims.items())}
    by_degree = {h: d for h, d in by_degree.items() if d}
    return {'reduced_rank': sum(by_degree.values()), 'by_degree': by_degree,
            'basis': sum(dims.values()), 'cube_states': 1 << n, 'entries': nnz}
