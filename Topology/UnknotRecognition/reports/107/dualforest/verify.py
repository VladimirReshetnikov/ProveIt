"""Source-bound combinatorial verifiers; imports no planner or intersection code.

These authenticate matrix/dual-graph claims, NOT the map from a triangulation to
that input. The existing native geometric source checker must still be run.
"""
from __future__ import annotations
from itertools import permutations
from .model import Instance


def _labels(values, bound):
    return (type(values) in (list, tuple) and
            all(type(x) is int and 0 <= x < bound for x in values) and
            len(set(values)) == len(values))


def _rank(inst, labels):
    adj = [set() for _ in range(inst.vertices)]
    for r in labels:
        a, b = inst.edges[r]
        adj[a].add(b)
        adj[b].add(a)
    seen = set()
    components = 0
    for a in range(inst.vertices):
        if a in seen:
            continue
        components += 1
        stack = [a]
        seen.add(a)
        while stack:
            v = stack.pop()
            for w in adj[v]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
    return inst.vertices - components


def _tree(inst, tree):
    return (_labels(tree, inst.m) and len(tree) == inst.vertices - 1 and
            _rank(inst, tree) == inst.vertices - 1)


def _timestamps(inst, deleted, pivots):
    if type(pivots) is not list:
        return False
    time = [-1 if r in deleted else None for r in range(inst.m)]
    pivot_column = {}
    for t, pair in enumerate(pivots):
        if type(pair) not in (list, tuple) or len(pair) != 2:
            return False
        r, c = pair
        if (type(r) is not int or not 0 <= r < inst.m or
                type(c) is not int or not 0 <= c < inst.columns or
                time[r] is not None or c in pivot_column):
            return False
        if dict(inst.rows[r]).get(c) != 1:
            return False
        time[r] = t
        pivot_column[c] = (r, t)
    if any(t is None for t in time):
        return False
    for r, row in enumerate(inst.rows):
        for c, _ in row:
            if c in pivot_column:
                p, t = pivot_column[c]
                if p != r and time[r] >= t:
                    return False
    return True


def verify_positive(inst: Instance, certificate: dict) -> bool:
    try:
        if type(certificate) is not dict or set(certificate) != {
                "schema", "tree", "dual_cancellations", "pivots"}:
            return False
        if certificate['schema'] != 'dual-forest-positive-v1':
            return False
        tree = certificate['tree']
        if not _tree(inst, tree):
            return False
        moves = certificate['dual_cancellations']
        if type(moves) is not list or len(moves) != len(tree):
            return False
        removed = {inst.root}
        used = set()
        for pair in moves:
            if type(pair) not in (list, tuple) or len(pair) != 2:
                return False
            r, child = pair
            if (type(r) is not int or r not in tree or r in used or
                    type(child) is not int or not 0 <= child < inst.vertices or
                    child in removed):
                return False
            a, b = inst.edges[r]
            if not ((a == child and b in removed) or (b == child and a in removed)):
                return False
            removed.add(child)
            used.add(r)
        return len(removed) == inst.vertices and _timestamps(inst, set(tree), certificate['pivots'])
    except (TypeError, ValueError, KeyError, IndexError):
        return False


def _source_analysis(inst):
    # Deliberately separate, simple polynomial construction. This verifier uses
    # repeated graph traversals instead of the producer's SCC routine.
    support = {}
    for r, row in enumerate(inst.rows):
        for c, w in row:
            support.setdefault(c, []).append((r, w))
    adj = [set() for _ in range(inst.m)]
    anchors = set()
    high = []
    for supp in support.values():
        units = {r for r, w in supp if w == 1}
        if not units:
            continue
        if len(supp) == 1:
            anchors.update(units)
        elif len(supp) == 2:
            (a, _), (b, _) = supp
            if a in units:
                adj[b].add(a)
            if b in units:
                adj[a].add(b)
        else:
            high.append(({r for r, _ in supp}, units))
    closure = []
    for a in range(inst.m):
        visited, todo = {a}, [a]
        while todo:
            u = todo.pop()
            for v in adj[u]:
                if v not in visited:
                    visited.add(v)
                    todo.append(v)
        closure.append(visited)
    remaining = set(range(inst.m))
    parts = []
    while remaining:
        a = min(remaining)
        part = {b for b in remaining if a in closure[b] and b in closure[a]}
        parts.append(part)
        remaining -= part
    source = [part for part in parts if not any(
        adj[u] & part for u in range(inst.m) if u not in part)]
    required = [part for part in source if not part & anchors]
    boundary = set().union(set(), *(supp for supp, _ in high))
    mandatory = [part for part in required if not part & boundary]
    available = set().union(set(), *(closure[r] for r in anchors))
    for part in mandatory:
        for r in part:
            available.update(closure[r])
    return closure, high, required, boundary, mandatory, available


def verify_pair_optimality(inst: Instance, certificate: dict) -> bool:
    try:
        if type(certificate) is not dict or set(certificate) != {
                'schema', 'tree', 'extra', 'pivots', 'obstruction_colors', 'defect'}:
            return False
        if certificate['schema'] != 'pair-defect-v1':
            return False
        _, high, groups, _, _, _ = _source_analysis(inst)
        if high:
            return False
        tree, extra = certificate['tree'], certificate['extra']
        defect = certificate['defect']
        if (not _tree(inst, tree) or not _labels(extra, inst.m) or
                set(tree) & set(extra) or type(defect) is not int or defect != len(extra)):
            return False
        if not _timestamps(inst, set(tree) | set(extra), certificate['pivots']):
            return False
        colors = certificate['obstruction_colors']
        if not _labels(colors, len(groups)):
            return False
        union = set().union(set(), *(groups[c] for c in colors))
        return len(colors) - _rank(inst, union) == defect
    except (TypeError, ValueError, KeyError, IndexError):
        return False


def _partitions(n):
    # A separate explicit-stack traversal of restricted-growth strings.
    if not n:
        yield ()
        return
    digits = [0] * n
    stack = [(1, 0, 0)]  # position, maximum used color, next color to try
    while stack:
        pos, maximum, color = stack[-1]
        if pos == n:
            yield tuple(tuple(i for i, d in enumerate(digits) if d == c)
                        for c in range(maximum + 1))
            stack.pop()
        elif color > maximum + 1:
            stack.pop()
        else:
            stack[-1] = (pos, maximum, color + 1)
            digits[pos] = color
            stack.append((pos + 1, max(maximum, color), 0))


def verify_negative(inst: Instance, certificate: dict, *, max_branches=None) -> bool:
    """Replay every branch's rank obstruction, with no matroid optimizer.

    This certifies only absence of a tree-plus-positive-pivot completion for
    the supplied matrix and dual graph. Verification can be FPT-expensive.
    """
    try:
        if (type(certificate) is not dict or set(certificate) != {'schema', 'rank_obstructions'}
                or certificate['schema'] != 'dual-forest-negative-v1'
                or type(certificate['rank_obstructions']) is not list):
            return False
        if max_branches is not None and (type(max_branches) is not int or max_branches < 0):
            return False
        closure, high, _, boundary, mandatory, base = _source_analysis(inst)
        if not high:
            return False  # low-column negatives use the stronger optimum certificate
        trace = certificate['rank_obstructions']
        index = 0
        for order in permutations(sorted(boundary)):
            prefix, available, special = set(), set(base), []
            for x in order:
                auto = x in available or any(x in unit and supp - {x} <= prefix
                                             for supp, unit in high)
                if not auto:
                    special.append({r for r in range(inst.m) if x in closure[r]})
                prefix.add(x)
                available.update(closure[x])
            for partition in _partitions(len(special)):
                if max_branches is not None and index >= max_branches:
                    return False
                if index >= len(trace):
                    return False
                groups = [set(g) for g in mandatory]
                for block in partition:
                    candidate = set(special[block[0]])
                    for i in block[1:]:
                        candidate &= special[i]
                    groups.append(candidate)
                colors = trace[index]
                index += 1
                if not _labels(colors, len(groups)):
                    return False
                union = set().union(set(), *(groups[c] for c in colors))
                if len(colors) <= _rank(inst, union):
                    return False
        return index == len(trace)
    except (TypeError, ValueError, KeyError, IndexError):
        return False
