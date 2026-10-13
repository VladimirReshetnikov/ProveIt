"""Graphic/partition matroid intersection, via shortest augmenting paths.

This is a specialization of the classical algorithm, not a new matroid theorem.
Only positive representatives or a Rado rank-deficiency certificate leave it.
"""
from __future__ import annotations
from collections import deque
from .model import Instance, DSU, rank


def transversal(inst: Instance, groups: list[set[int]], *, check=lambda: None) -> dict:
    clones = [(r, color) for color, group in enumerate(groups) for r in sorted(group)]
    selected: set[int] = set()
    augments = 0
    while True:
        check()
        forest = [[] for _ in range(inst.vertices)]
        d = DSU(inst.vertices)
        occupant = {}
        for i in sorted(selected):
            r, color = clones[i]
            u, v = inst.edges[r]
            joined = d.union(u, v)  # Never hide a state change inside an assert.
            if not joined or color in occupant:
                raise AssertionError("selected clones lost common independence")
            occupant[color] = i
            forest[u].append((v, i))
            forest[v].append((u, i))
        outgoing = {i: [] for i in selected}
        sources = []
        # Each selected forest path gives exactly the fundamental-circuit exchanges.
        for j, (r, color) in enumerate(clones):
            check()
            if j in selected:
                continue
            u, v = inst.edges[r]
            if d.find(u) != d.find(v):
                sources.append(j)
                continue
            if u == v:
                continue
            parent = {u: (None, None)}
            queue = [u]
            while queue and v not in parent:
                a = queue.pop()
                for b, i in forest[a]:
                    if b not in parent:
                        parent[b] = (a, i)
                        queue.append(b)
            a = v
            while a != u:
                b, i = parent[a]
                outgoing[i].append(j)
                a = b
        pred = {j: None for j in sources}
        queue = deque(sources)
        sink = None
        while queue:
            j = queue.popleft()
            if j in selected:
                nexts = outgoing[j]
            else:
                color = clones[j][1]
                if color not in occupant:
                    sink = j
                    break
                nexts = [occupant[color]]
            for k in nexts:
                if k not in pred:
                    pred[k] = j
                    queue.append(k)
        if sink is None:
            represented = [(clones[i][0], clones[i][1]) for i in sorted(selected)]
            seen_colors = {clones[j][1] for j in pred}
            deficient = sorted(set(range(len(groups))) - seen_colors)
            union = set().union(set(), *(groups[c] for c in deficient))
            defect = len(groups) - len(selected)
            assert len(deficient) - rank(inst, union) == defect
            return dict(representatives=[list(t) for t in represented],
                        size=len(selected), defect=defect,
                        obstruction_colors=deficient, augments=augments,
                        clone_count=len(clones))
        path = []
        while sink is not None:
            path.append(sink)
            sink = pred[sink]
        selected.symmetric_difference_update(path)
        augments += 1
