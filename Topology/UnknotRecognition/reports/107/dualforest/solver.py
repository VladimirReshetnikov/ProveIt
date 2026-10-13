"""Exact local selectors. A local negative result is NOT a topology verdict."""
from __future__ import annotations
from collections import deque
from itertools import permutations
from .model import Instance, extend_tree
from .dependencies import build, requirements, branch_groups, partitions, peel
from .intersection import transversal


def positive_certificate(inst: Instance, tree: list[int]) -> dict | None:
    pivots = peel(inst, tree)
    if pivots is None:
        return None
    adj = [[] for _ in range(inst.vertices)]
    for r in tree:
        a, b = inst.edges[r]
        adj[a].append((b, r))
        adj[b].append((a, r))
    visited = {inst.root}
    queue = deque([inst.root])
    dual = []
    while queue:
        a = queue.popleft()
        for b, r in sorted(adj[a]):
            if b not in visited:
                visited.add(b)
                queue.append(b)
                dual.append([r, b])
    return dict(schema="dual-forest-positive-v1", tree=sorted(tree),
                dual_cancellations=dual, pivots=pivots)


def solve_pair(inst: Instance, *, check=lambda: None) -> dict:
    """Exact minimum extra-deletion defect for all low-usable-column inputs.

    High-support columns with no unit entry are harmless and allowed.
    A negative status refers only to the fixed cancellation selection problem.
    """
    check()
    info = build(inst)
    check()
    if info['boundary']:
        raise ValueError("pair solver does not accept usable high-support columns")
    groups = info['required']
    ans = transversal(inst, groups, check=check)
    tree = extend_tree(inst, (r for r, _ in ans['representatives']))
    unhit = [part for part in groups if not part & set(tree)]
    extra = sorted(min(part) for part in unhit)
    assert len(extra) == ans['defect']
    pivots_with_extra = peel(inst, set(tree) | set(extra))
    assert pivots_with_extra is not None
    opt = dict(schema="pair-defect-v1", tree=tree, extra=extra,
               pivots=pivots_with_extra,
               obstruction_colors=ans['obstruction_colors'], defect=ans['defect'])
    cert = positive_certificate(inst, tree) if not extra else None
    return dict(status="yes" if cert else "no", certificate=cert,
                optimality=opt, stats=dict(branches=1, boundary_rows=0,
                                          clones=ans['clone_count'],
                                          augments=ans['augments']))


def solve(inst: Instance, *, max_branches: int | None = None,
          try_incumbent: bool = True, retain_negative: bool = True,
          check=lambda: None) -> dict:
    """FPT exact solver, with an explicit Unknown when a branch cap is hit.

    max_branches counts intersection subproblems, not wall time. It cannot
    bound source parsing or dependency preparation. It never converts a cap
    into a negative answer. An optional successful incumbent returns its proof.
    """
    check()
    if max_branches is not None and (type(max_branches) is not int or max_branches < 0):
        raise ValueError("max_branches must be a nonnegative integer or None")
    if try_incumbent:
        cert = positive_certificate(inst, extend_tree(inst, []))
        if cert is not None:
            return dict(status="yes", certificate=cert,
                        stats=dict(branches=0, route="incumbent"))
    check()
    info = build(inst)
    check()
    if not info['boundary']:
        if max_branches == 0:
            return dict(status="unknown", certificate=None,
                        stats=dict(branches=0, boundary_rows=0))
        return solve_pair(inst, check=check)
    branches = 0
    trace = []
    b = len(info['boundary'])
    for order in permutations(sorted(info['boundary'])):
        special = requirements(info, order)
        for partition in partitions(len(special)):
            check()
            if max_branches is not None and branches >= max_branches:
                return dict(status="unknown", certificate=None,
                            stats=dict(branches=branches, boundary_rows=b))
            groups = branch_groups(info, order, partition)
            ans = transversal(inst, groups, check=check)
            branches += 1
            if ans['defect'] == 0:
                tree = extend_tree(inst, (r for r, _ in ans['representatives']))
                cert = positive_certificate(inst, tree)
                if cert is None:
                    raise AssertionError("a branch witness failed independent full-matrix peeling")
                return dict(status="yes", certificate=cert,
                            witness=dict(order=list(order),
                                         partition=[list(c) for c in partition],
                                         representatives=ans['representatives']),
                            stats=dict(branches=branches, boundary_rows=b))
            if retain_negative:
                trace.append(ans['obstruction_colors'])
    negative = dict(schema="dual-forest-negative-v1", rank_obstructions=trace) if retain_negative else None
    return dict(status="no", certificate=None, negative_certificate=negative,
                stats=dict(branches=branches, boundary_rows=b))
