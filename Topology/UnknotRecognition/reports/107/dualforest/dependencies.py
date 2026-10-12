"""Low-column dependency graph and high-support obligations."""
from __future__ import annotations
from collections import deque
from itertools import permutations
from .model import Instance


def columns(inst: Instance) -> dict[int, list[tuple[int, int]]]:
    ans: dict[int, list[tuple[int, int]]] = {}
    for r, row in enumerate(inst.rows):
        for c, w in row:
            ans.setdefault(c, []).append((r, w))
    return ans


def reach(adj: list[set[int]], seeds) -> set[int]:
    seen = set(seeds)
    todo = list(seen)
    while todo:
        x = todo.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return seen


def scc(adj: list[set[int]]) -> list[set[int]]:
    """Iterative Kosaraju: no recursion proportional to the source size."""
    n = len(adj)
    rev = [set() for _ in range(n)]
    for u in range(n):
        for v in adj[u]:
            rev[v].add(u)
    seen, order = set(), []
    for root in range(n):
        if root in seen:
            continue
        seen.add(root)
        stack = [(root, iter(sorted(adj[root])))]
        while stack:
            u, it = stack[-1]
            try:
                v = next(it)
            except StopIteration:
                order.append(u)
                stack.pop()
                continue
            if v not in seen:
                seen.add(v)
                stack.append((v, iter(sorted(adj[v]))))
    seen, parts = set(), []
    for root in reversed(order):
        if root in seen:
            continue
        block = {root}
        seen.add(root)
        todo = [root]
        while todo:
            u = todo.pop()
            for v in rev[u]:
                if v not in seen:
                    seen.add(v)
                    block.add(v)
                    todo.append(v)
        parts.append(block)
    return sorted(parts, key=lambda b: min(b))


def build(inst: Instance) -> dict:
    adj = [set() for _ in range(inst.m)]
    anchor = set()
    high = []
    for c, supp in sorted(columns(inst).items()):
        if not any(w == 1 for _, w in supp):
            continue
        if len(supp) == 1:
            anchor.add(supp[0][0])
        elif len(supp) == 2:
            (u, a), (v, b) = supp
            if a == 1:
                adj[v].add(u)
            if b == 1:
                adj[u].add(v)
        else:
            high.append((c, frozenset(r for r, _ in supp),
                         frozenset(r for r, w in supp if w == 1)))
    rev = [set() for _ in range(inst.m)]
    for u in range(inst.m):
        for v in adj[u]:
            rev[v].add(u)
    parts = scc(adj)
    owner = {r: i for i, part in enumerate(parts) for r in part}
    incoming = [False] * len(parts)
    for u in range(inst.m):
        for v in adj[u]:
            if owner[u] != owner[v]:
                incoming[owner[v]] = True
    source = [part for i, part in enumerate(parts) if not incoming[i]]
    required = [part for part in source if not part & anchor]
    boundary = set().union(*(s for _, s, _ in high)) if high else set()
    mandatory = [part for part in required if not part & boundary]
    initially = reach(adj, anchor | set().union(set(), *mandatory))
    return dict(adj=adj, rev=rev, anchors=anchor, high=high, boundary=boundary,
                required=required, mandatory=mandatory, initially=initially,
                forward={r: reach(adj, [r]) for r in boundary},
                ancestors={r: reach(rev, [r]) for r in boundary})


def requirements(info: dict, order: tuple[int, ...]) -> list[set[int]]:
    prefix = set()
    accessible = set(info['initially'])
    special = []
    for x in order:
        ready = x in accessible or any(
            x in units and supp - {x} <= prefix
            for _, supp, units in info['high'])
        if not ready:
            special.append(info['ancestors'][x])
        prefix.add(x)
        accessible.update(info['forward'][x])
    return special


def partitions(n: int):
    """Iterative restricted-growth enumeration; no Python recursion limit."""
    if n == 0:
        yield ()
        return
    digits = [0] * n
    while True:
        blocks = [[] for _ in range(max(digits) + 1)]
        for i, color in enumerate(digits):
            blocks[color].append(i)
        yield tuple(tuple(block) for block in blocks)
        # Increment the last legal restricted-growth digit, resetting its suffix.
        prefix_max = [0] * n
        for i in range(1, n):
            prefix_max[i] = max(prefix_max[i-1], digits[i-1])
        for i in range(n-1, 0, -1):
            if digits[i] < prefix_max[i] + 1:
                digits[i] += 1
                digits[i+1:] = [0] * (n-i-1)
                break
        else:
            return


def branch_groups(info: dict, order, partition) -> list[set[int]]:
    special = requirements(info, order)
    groups = [set(b) for b in info['mandatory']]
    for block in partition:
        joint = set(special[block[0]])
        for j in block[1:]:
            joint.intersection_update(special[j])
        groups.append(joint)
    return groups


def peel(inst: Instance, deleted) -> list[list[int]] | None:
    """Static queue. Returns all row/column pivots or None; no positive fill."""
    live = set(range(inst.m)) - set(deleted)
    cc = columns(inst)
    supports = {c: {r for r, _ in values if r in live} for c, values in cc.items()}
    weight = {(r, c): w for r, row in enumerate(inst.rows) for c, w in row}
    todo = deque(c for c, ss in sorted(supports.items()) if len(ss) == 1)
    pivots = []
    while todo:
        c = todo.popleft()
        if len(supports[c]) != 1:
            continue
        r = next(iter(supports[c]))
        if weight[r, c] != 1:
            continue
        pivots.append([r, c])
        live.remove(r)
        for h, _ in inst.rows[r]:
            supports[h].remove(r)
            if len(supports[h]) == 1:
                todo.append(h)
    return None if live else pivots
