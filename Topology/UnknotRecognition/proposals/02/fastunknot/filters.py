"""Exact, one-sided modular obstructions. Equality with the unknot proves nothing.

Jones evaluation uses an independent pairing-state engine (not the cobordism
engine). All arithmetic is deterministic. A nonzero discrepancy is a proof
of knottedness, not a probabilistic guess.
"""
from __future__ import annotations

from collections import defaultdict
from time import monotonic
from typing import Iterable

from .diagram import Diagram, DisjointSet
from .scan import ScanLimit, best_scan_order, validate_order

PRIME = 1_000_000_007


class FilterLimit(RuntimeError):
    """The bounded prefilter stopped. Continue with the complete fallback."""


def _check(deadline: float | None) -> None:
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("time budget exhausted")


def oriented_writhe(diagram: Diagram) -> int:
    """Geometric writhe, including the direction of BOTH strands at each crossing.

    The inherited Diagram.signs() is a local Fox-row convention and must not be
    used here on arbitrary PD codes: the incoming under-port need not be slot 0.
    """
    incoming = [[0, 0] for _ in diagram.pd]
    for dart in diagram.traversal():
        incoming[dart // 4][dart % 2] = dart % 4
    return sum(1 if (over - under) % 4 == 3 else -1 for under, over in incoming)


def determinant_residue(diagram: Diagram, *, deadline: float | None = None) -> dict:
    """Determinant of a Fox minor at t=-1, modulo a fixed prime.

    Sparse row Gaussian elimination is O(n^3) field operations in the worst
    case and O(n^2) storage. The returned residue is allowed a sign ambiguity.
    """
    _check(deadline)
    n = diagram.crossings
    if n == 0:
        return {"prime": PRIME, "residue": 1, "obstructs": False}
    arcs = DisjointSet(2 * n)
    for _, b, _, d in diagram.pd:
        arcs.union(b, d)
    roots = sorted({arcs.find(e) for e in range(2 * n)})
    if len(roots) != n:
        raise ArithmeticError("unexpected number of Wirtinger arcs")
    col = {root: i for i, root in enumerate(roots)}
    rows = []
    for a, b, c, _ in diagram.pd[:-1]:
        row = {}
        for edge, coefficient in ((b, 2), (a, -1), (c, -1)):
            j = col[arcs.find(edge)]
            if j < n - 1:
                row[j] = (row.get(j, 0) + coefficient) % PRIME
        rows.append({j: x for j, x in row.items() if x})
    value = 1
    size = n - 1
    updates = 0
    for k in range(size):
        _check(deadline)
        pivot_row = min((i for i in range(k, size) if rows[i].get(k)),
                        key=lambda i: (len(rows[i]), i), default=None)
        if pivot_row is None:
            value = 0
            break
        if pivot_row != k:
            rows[k], rows[pivot_row] = rows[pivot_row], rows[k]
            value = -value
        pivot = rows[k][k]
        value = value * pivot % PRIME
        inv = pow(pivot, -1, PRIME)
        entries = [(j, x) for j, x in rows[k].items() if j > k]
        for i in range(k + 1, size):
            if i % 64 == 0:
                _check(deadline)
            row = rows[i]
            coefficient = row.pop(k, 0)
            if not coefficient:
                continue
            factor = coefficient * inv % PRIME
            for j, x in entries:
                y = (row.get(j, 0) - factor * x) % PRIME
                if y:
                    row[j] = y
                else:
                    row.pop(j, None)
                updates += 1
    value %= PRIME
    return {"prime": PRIME, "residue": value, "obstructs": value not in (1, PRIME - 1),
            "entry_updates": updates}


Pairing = tuple[tuple[int, int], ...]


def _attach(pairing: Pairing, slots: tuple[int, ...], smoothing: int,
            boundary: frozenset[int]) -> tuple[Pairing, int]:
    """Attach a smoothing by union-find on edge labels. Independent of scan.glue."""
    parent = {x: x for pair in pairing for x in pair}
    parent.update({x: x for x in slots})

    def find(x):
        root = x
        while parent[root] != root:
            root = parent[root]
        while parent[x] != root:
            parent[x], x = root, parent[x]
        return root

    for a, b in pairing:
        parent[find(a)] = find(b)
    a, b, c, d = slots
    for x, y in (((a, b), (c, d)) if smoothing == 0 else ((a, d), (b, c))):
        parent[find(x)] = find(y)
    groups = defaultdict(list)
    for x in parent:
        root = find(x)
        if x in boundary:
            groups[root].append(x)
        else:
            groups.setdefault(root, [])
    output = []
    closed = 0
    for ends in groups.values():
        if not ends:
            closed += 1
        elif len(ends) == 2:
            output.append(tuple(sorted(ends)))
        else:
            raise ArithmeticError("a frontier component must have zero or two ends")
    return tuple(sorted(output)), closed


def jones_evaluation(diagram: Diagram, *, order: Iterable[int] | None = None,
                     value: int = 2, max_states: int | None = 50_000,
                     max_transitions: int | None = 1_000_000,
                     deadline: float | None = None) -> dict:
    """Evaluate the all-loops bracket modulo PRIME and compare with the unknot.

    Smoothing 0 has coefficient A, smoothing 1 has coefficient A^{-1}, and a
    circle has value delta=-A^2-A^{-2}. For the PD convention in this package
    a writhe +1 curl contributes -A^3. Hence the unknot comparison is
    bracket == delta * (-A^3)^w. No division by delta is performed.

    Without caps, the frontier bound is O(n poly(w) (w-1)!!) field operations,
    for maximum boundary size w (using the maximum over all stages). This is a
    Jones filter, NOT a complete unknot algorithm. Resource caps raise
    FilterLimit, never a topological verdict.
    """
    _check(deadline)
    if type(value) is not int or value % PRIME == 0:
        raise ValueError("A must be an integer nonzero modulo the fixed prime")
    for name, cap in (("max_states", max_states), ("max_transitions", max_transitions)):
        if cap is not None and (type(cap) is not int or cap < 1):
            raise ValueError(f"{name} must be a positive integer or None")
    pd = diagram.pd
    order = (best_scan_order(pd, tries=min(len(pd), 12)) if pd else []) if order is None \
        else validate_order(len(pd), order)
    value %= PRIME
    inverse = pow(value, -1, PRIME)
    delta = -(value * value + inverse * inverse) % PRIME
    coefficients = (value, inverse)
    states: dict[Pairing, int] = {(): 1}
    boundary = set()
    maximum = 1
    width = transitions = 0
    for index in order:
        _check(deadline)
        slots = pd[index]
        for e in slots:
            boundary.symmetric_difference_update((e,))
        frozen_boundary = frozenset(boundary)
        width = max(width, len(boundary))
        target = {}
        for pairing, coefficient in states.items():
            for smoothing in (0, 1):
                if max_transitions is not None and transitions >= max_transitions:
                    raise FilterLimit("Jones transition budget exhausted")
                if transitions % 256 == 0:
                    _check(deadline)
                output, closed = _attach(pairing, slots, smoothing, frozen_boundary)
                weight = coefficient * coefficients[smoothing] * pow(delta, closed, PRIME)
                total = (target.get(output, 0) + weight) % PRIME
                if total:
                    target[output] = total
                    if max_states is not None and len(target) > max_states:
                        raise FilterLimit("Jones state budget exhausted")
                else:
                    target.pop(output, None)
                transitions += 1
        states = target
        maximum = max(maximum, len(states))
    bracket = states.get((), 0) if pd else delta
    writhe = oriented_writhe(diagram)
    expected = delta * pow((-pow(value, 3, PRIME)) % PRIME, writhe, PRIME) % PRIME
    return {"prime": PRIME, "A": value, "writhe": writhe,
            "bracket": bracket, "unknot_bracket": expected,
            "obstructs": bracket != expected,
            "order": order, "max_states": maximum, "max_boundary": width,
            "transitions": transitions}
