"""Exact, weighted representative families for boundary-arc disk completion.

This is a finite surface-frontier kernel, NOT an unknot recognizer.
Partitions describe actual disjoint gluing arcs, not arbitrary port unions.
Only Python's standard library is required.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable, Sequence

Partition = tuple[int, ...]

class ResourceLimit(RuntimeError):
    """A resource cap was reached; no mathematical negative answer follows."""


def validate_partition(p: Sequence[int], *, max_width: int = 20) -> Partition:
    if type(max_width) is not int or max_width < 1:
        raise ValueError("max_width must be a positive integer")
    p = tuple(p)
    if not p:
        raise ValueError("use a separate terminal rule for the empty interface")
    if len(p) > max_width:
        raise ResourceLimit(f"interface width {len(p)} exceeds cap {max_width}")
    largest = -1
    for a in p:
        if type(a) is not int or a < 0 or a > largest + 1:
            raise ValueError("partition must be a restricted-growth integer tuple")
        largest = max(largest, a)
    return p


def canonical(labels: Iterable[object]) -> Partition:
    names: dict[object, int] = {}
    out = []
    for x in labels:
        if x not in names:
            names[x] = len(names)
        out.append(names[x])
    return tuple(out)


def partitions(r: int) -> Iterable[Partition]:
    if type(r) is not int or r < 1:
        raise ValueError("r must be a positive integer")
    def visit(prefix: list[int], largest: int):
        if len(prefix) == r:
            yield tuple(prefix)
            return
        for a in range(largest + 2):
            yield from visit(prefix + [a], max(largest, a))
    yield from visit([0], 0)


def root_row(p: Sequence[int], *, max_width: int = 20,
             check: Callable[[], None] | None = None) -> int:
    """Bit m indicates that {0} union bits(m)+1 is a transversal of p.

    The integer has at most 2**(r-1) bits. That exponential allocation is
    charged explicitly; max_width is checked before constructing it.
    """
    p = validate_partition(p, max_width=max_width)
    blocks: list[list[int]] = [[] for _ in range(max(p) + 1)]
    for i, a in enumerate(p):
        blocks[a].append(i)
    ans = 0
    # Block zero contains distinguished port zero; its chosen root is fixed.
    for roots in product(*blocks[1:]):
        if check is not None:
            check()
        mask = sum(1 << (i - 1) for i in roots)
        ans |= 1 << mask
    return ans


@dataclass(frozen=True)
class Candidate:
    partition: Partition
    cost: int
    witness: tuple[int, ...] = ()


@dataclass(frozen=True)
class Reduction:
    retained: tuple[Candidate, ...]
    certificate: dict


def reduce_family(items: Sequence[Candidate], *, max_width: int = 20,
                  check: Callable[[], None] | None = None) -> Reduction:
    """Preserve the minimum cost of completion against EVERY disk-union cap.

    All candidates must share one geometric/boundary type. The caller, not
    this function, is responsible for authenticating that condition.
    Each discarded row is certified as an XOR of no-more-expensive retained
    ORIGINAL rows; linear combinations are never substituted for surfaces.
    """
    items = tuple(items)
    if not items:
        return Reduction((), {"version": 1, "width": 0,
                              "retained": [], "expansions": []})
    r = len(items[0].partition)
    for x in items:
        validate_partition(x.partition, max_width=max_width)
        if len(x.partition) != r or type(x.cost) is not int:
            raise ValueError("inconsistent widths or non-integer cost")
    order = sorted(range(len(items)), key=lambda i: (items[i].cost, i))
    basis: dict[int, tuple[int, int]] = {}
    keep: list[int] = []
    expressions = [0] * len(items)
    for i in order:
        if check is not None:
            check()
        row = root_row(items[i].partition, max_width=max_width, check=check)
        combination = 0
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                pos = len(keep)
                keep.append(i)
                basis[pivot] = (row, combination ^ (1 << pos))
                expressions[i] = 1 << pos
                break
            vector, expression = basis[pivot]
            row ^= vector
            combination ^= expression
        else:
            expressions[i] = combination
    cert = {
        "version": 1, "width": r, "retained": keep,
        "expansions": [[keep[j] for j in range(len(keep)) if e >> j & 1]
                       for e in expressions],
    }
    return Reduction(tuple(items[i] for i in keep), cert)


def disk_compatible(p: Sequence[int], q: Sequence[int]) -> bool:
    """Direct union-find tree test; does not use the transversal identity."""
    p = validate_partition(p)
    q = validate_partition(q)
    if len(p) != len(q):
        raise ValueError("interface widths differ")
    cp, cq = max(p) + 1, max(q) + 1
    if cp + cq != len(p) + 1:
        return False
    parent = list(range(cp + cq))
    def find(a: int) -> int:
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for a, b in zip(p, q):
        a, b = find(a), find(cp + b)
        if a == b:
            return False
        parent[a] = b
    return True  # |E|=|V|-1 and no cycles implies connected.


def minimum_completion(items: Sequence[Candidate], cap: Sequence[int]) -> Candidate | None:
    feasible = [x for x in items if disk_compatible(x.partition, cap)]
    return min(feasible, key=lambda x: (x.cost, x.witness)) if feasible else None
