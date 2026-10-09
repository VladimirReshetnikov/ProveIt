"""Independent reduced F2 Khovanov cube; validation oracle, exponential cost."""
from __future__ import annotations
from collections import defaultdict
from .diagram import Diagram


def binary_rank(columns):
    pivots = {}
    for column in columns:
        while column:
            p = column.bit_length() - 1
            if p in pivots:
                column ^= pivots[p]
            else:
                pivots[p] = column
                break
    return len(pivots)


def reduced_homology(diagram: Diagram, *, max_crossings=12, max_generators=250000, check_d2=True):
    n = len(diagram.pd)
    if n > max_crossings:
        raise ValueError("reference cube crossing budget exceeded")
    circles = [diagram.state_circles(s) for s in range(1 << n)]
    owners = [{d: i for i, c in enumerate(cs) for d in c} for cs in circles]
    # Dart zero, or the first explicitly supplied free circle, carries the mark.
    marks = [owner[0] for owner in owners]
    groups, coordinates = defaultdict(list), {}
    total = 0
    for s, cs in enumerate(circles):
        marker = marks[s]
        unmarked = [i for i in range(len(cs)) if i != marker]
        for labels in range(1 << len(unmarked)):
            mask = 1 << marker
            for j, i in enumerate(unmarked):
                if labels >> j & 1:
                    mask |= 1 << i
            h = s.bit_count()
            q = h + len(unmarked) - 2 * labels.bit_count()
            key = (h, q)
            coordinates[s, mask] = (key, len(groups[key]))
            groups[key].append((s, mask))
            total += 1
            if total > max_generators:
                raise ValueError("reference cube generator budget exceeded")
    plans = {}
    for s in range(1 << n):
        for v in range(n):
            if s >> v & 1:
                continue
            t = s | (1 << v)
            associations = [set(owners[t][d] for d in c) for c in circles[s]]
            inverse = defaultdict(list)
            for i, js in enumerate(associations):
                for j in js:
                    inverse[j].append(i)
            if len(circles[t]) == len(circles[s]) - 1:
                target = next(j for j, old in inverse.items() if len(old) == 2)
                affected = tuple(inverse[target])
                ordinary = tuple((i, next(iter(js))) for i, js in enumerate(associations) if i not in affected)
                plans[s, v] = (t, 'merge', affected, (target,), ordinary)
            elif len(circles[t]) == len(circles[s]) + 1:
                source = next(i for i, js in enumerate(associations) if len(js) == 2)
                ordinary = tuple((i, next(iter(js))) for i, js in enumerate(associations) if i != source)
                plans[s, v] = (t, 'split', (source,), tuple(sorted(associations[source])), ordinary)
            else:
                raise ArithmeticError("nonclassical saddle")
    differential = {}
    for key, basis in groups.items():
        h, q = key
        columns = []
        for s, mask in basis:
            column = 0
            for v in range(n):
                if s >> v & 1:
                    continue
                t, kind, old, new, ordinary = plans[s, v]
                base = sum(1 << j for i, j in ordinary if mask >> i & 1)
                if kind == 'merge':
                    dots = sum((mask >> i) & 1 for i in old)
                    targets = [] if dots == 2 else [base | ((1 << new[0]) if dots else 0)]
                else:
                    a, b = new
                    targets = [base | (1 << a) | (1 << b)] if mask >> old[0] & 1 else [base | (1 << a), base | (1 << b)]
                for target in targets:
                    target_key, row = coordinates[t, target]
                    if target_key != (h + 1, q):
                        raise ArithmeticError("differential lost quantum grading")
                    column ^= 1 << row
            columns.append(column)
        differential[key] = columns
    checked = 0
    if check_d2:
        for (h, q), columns in differential.items():
            nxt = differential.get((h + 1, q), [])
            for column in columns:
                image = 0
                while column:
                    bit = column & -column
                    image ^= nxt[bit.bit_length() - 1]
                    column ^= bit
                if image:
                    raise ArithmeticError("d squared is not zero")
                checked += 1
    ranks = {key: binary_rank(columns) for key, columns in differential.items()}
    homology = {}
    for (h, q), basis in groups.items():
        dim = len(basis) - ranks.get((h, q), 0) - ranks.get((h - 1, q), 0)
        if dim < 0:
            raise ArithmeticError("negative homology dimension")
        if dim:
            homology[h, q] = dim
    return dict(rank=sum(homology.values()), generators=total, d2_columns=checked,
                bigraded=[dict(h=h, q=q, rank=r) for (h,q),r in sorted(homology.items())])
