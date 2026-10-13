"""Classical graphic/partition matroid intersection with a fixed contracted forest.

This intentionally straightforward oracle implementation is independent of the
vendored predecessor. Mandatory color classes must be disjoint. It produces
actual edges, not algebraic linear combinations.
"""
from __future__ import annotations
from collections import deque
from .model import Instance, forest, DSU


def representatives(inst: Instance, groups: list[set[int]], fixed=()) -> dict:
    fixed = tuple(fixed)
    if not forest(inst, fixed):
        raise ValueError('fixed edges are dependent')
    color = {}
    for i, group in enumerate(groups):
        for e in group:
            if e in color:
                raise ValueError('this specialized oracle requires disjoint color classes')
            color[e] = i
    ground = sorted(set(color) - set(fixed))
    selected: set[int] = set()
    augmentations = 0
    while True:
        owner = {color[e]: e for e in selected}
        sources = [e for e in ground if e not in selected and forest(inst, (*fixed, *selected, e))]
        pred = {e: None for e in sources}
        queue = deque(sources)
        sink = None
        while queue:
            x = queue.popleft()
            if x in selected:
                nxt = [e for e in ground if e not in selected
                       and forest(inst, (*fixed, *(selected - {x}), e))]
            elif color[x] not in owner:
                sink = x
                break
            else:
                nxt = [owner[color[x]]]
            for y in nxt:
                if y not in pred:
                    pred[y] = x
                    queue.append(y)
        if sink is None:
            seen = {color[e] for e in pred}
            return dict(edges=sorted(selected), complete=len(selected) == len(groups),
                        obstruction_colors=sorted(set(range(len(groups))) - seen),
                        augmentations=augmentations)
        while sink is not None:
            if sink in selected:
                selected.remove(sink)
            else:
                selected.add(sink)
            sink = pred[sink]
        augmentations += 1
        if not forest(inst, (*fixed, *selected)) or len({color[e] for e in selected}) != len(selected):
            raise AssertionError('shortest augmentation lost independence')


def graphic_rank(inst: Instance, edges) -> int:
    d = DSU(inst.vertices)
    answer = 0
    for e in edges:
        answer += d.union(*inst.edges[e])
    return answer
