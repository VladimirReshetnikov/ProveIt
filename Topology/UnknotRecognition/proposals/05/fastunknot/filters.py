"""Exact, one-sided modular obstructions to being an unknot.

A mismatch is a proof of KNOTTED; a match or budget exhaustion is inconclusive.
No probabilistic verdicts, floating-point topology, or optional dependencies.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from time import monotonic
from typing import Any, Iterable

from .diagram import Diagram, DisjointSet
from .scan import ScanLimit, best_scan_order

MODULUS = 2_147_483_647  # Mersenne prime 2^31 - 1; all arithmetic is exact.
PAIRINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))
Pairing = tuple[tuple[int, int], ...]


def _check(deadline: float | None) -> None:
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("time budget exhausted")


def sparse_determinant(matrix: list[dict[int, int]], p: int = MODULUS,
                       *, deadline: float | None = None) -> int:
    """Gaussian elimination over F_p, with sparse rows and fixed column order.

    p must be prime. The recognizer always uses the fixed prime MODULUS.
    The input is copied. Dense worst case: O(n^3) field operations.
    """
    n = len(matrix)
    a = [{j: x % p for j, x in row.items() if x % p} for row in matrix]
    determinant = 1
    for k in range(n):
        _check(deadline)
        pivot_row = next((i for i in range(k, n) if a[i].get(k, 0)), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            determinant = -determinant
        pivot = a[k][k]
        determinant = determinant * pivot % p
        inv = pow(pivot, -1, p)
        tail = [(j, x) for j, x in a[k].items() if j > k]
        for i in range(k + 1, n):
            if i % 64 == 0:
                _check(deadline)
            coefficient = a[i].pop(k, 0)
            if not coefficient:
                continue
            factor = coefficient * inv % p
            row = a[i]
            for j, x in tail:
                value = (row.get(j, 0) - factor * x) % p
                if value:
                    row[j] = value
                else:
                    row.pop(j, None)
    return determinant % p


def determinant_obstruction(diagram: Diagram, *, deadline: float | None = None) -> dict:
    """A(-1) minor modulo p; an unknot's value MUST be +1 or -1.

    At t=-1 the sign of each Wirtinger crossing disappears: row entries
    are 2 on the over arc and -1 on each under arc.
    """
    n = diagram.crossings
    if n == 0:
        return {'detected': False, 'modulus': MODULUS, 'minor_residue': 1}
    _check(deadline)
    arcs = DisjointSet(2 * n)
    for _, b, _, d in diagram.pd:
        arcs.union(b, d)
    roots = sorted({arcs.find(e) for e in range(2 * n)})
    if len(roots) != n:
        raise ArithmeticError('unexpected number of Wirtinger arcs')
    col = {r: i for i, r in enumerate(roots)}
    rows = []
    for a, b, c, _ in diagram.pd[:-1]:
        row = {}
        for edge, value in ((b, 2), (a, -1), (c, -1)):
            j = col[arcs.find(edge)]
            if j < n - 1:
                row[j] = row.get(j, 0) + value
        rows.append(row)
    residue = sparse_determinant(rows, deadline=deadline)
    return {'detected': residue not in (1, MODULUS - 1),
            'modulus': MODULUS, 'evaluation_t': -1, 'minor_residue': residue,
            'unknot_residues': [1, MODULUS - 1]}


def attach(matching: Pairing, slots: tuple[int, int, int, int],
           smoothing: int) -> tuple[Pairing, int]:
    """Independent pairing transition, not the cobordism backend's glue code.

    The union of the matching and the smoothing is a degree <=2 multigraph.
    Its path components give the new matching; its cycles give closed circles.
    Repeated labels and self-loop edges are treated with multiplicity.
    """
    parent: dict[int, int] = {}
    degree: dict[int, int] = {}

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def add(a: int, b: int) -> None:
        for x in (a, b):
            parent.setdefault(x, x)
            degree[x] = degree.get(x, 0) + 1
        x, y = find(a), find(b)
        if x != y:
            parent[x] = y

    for a, b in matching:
        add(a, b)
    for a, b in PAIRINGS[smoothing]:
        add(slots[a], slots[b])
    groups: dict[int, list[int]] = {}
    for x in parent:
        group = groups.setdefault(find(x), [])
        if degree[x] == 1:
            group.append(x)
        elif degree[x] != 2:
            raise ArithmeticError('invalid pairing transition degree')
    pairs, closed = [], 0
    for group in groups.values():
        if not group:
            closed += 1
        elif len(group) == 2:
            pairs.append(tuple(sorted(group)))
        else:
            raise ArithmeticError('path component has unexpected endpoints')
    return tuple(sorted(pairs)), closed


def bracket_obstruction(diagram: Diagram, *, order: Iterable[int] | None = None,
                        modulus: int | None = MODULUS, value: int = 2,
                        max_transitions: int | None = None,
                        max_states: int | None = None,
                        deadline: float | None = None) -> dict[str, Any]:
    """Evaluate the unnormalized Kauffman bracket and compare with the unknot.

    The loop scalar is delta=-A^2-A^-2 and a crossing contributes
    A * smoothing_0 + A^-1 * smoothing_1.  For an unknot diagram of
    oriented writhe w the result is delta*(-A^3)^w.

    Budget exhaustion returns complete=False, NEVER detected=True.
    With modulus=None, evaluate exactly at integer A after multiplying the
    bracket by A^(5n) (by A^2 for n=0). Large integers are serialized in hex.
    A composite modulus is also valid provided A is a unit: only the
    Laurent-polynomial identity, not field elimination, is used here.
    """
    if modulus is not None and (type(modulus) is not int or modulus < 2):
        raise ValueError('modulus must be an integer >= 2 or None')
    if modulus is None:
        if type(value) is not int or value < 2:
            raise ValueError('integer evaluation requires A >= 2')
    elif type(value) is not int or gcd(value, modulus) != 1:
        raise ValueError('A must be an integer unit modulo the modulus')
    for name, limit in (('max_transitions', max_transitions), ('max_states', max_states)):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError(name + ' must be a nonnegative integer')
    _check(deadline)
    n = diagram.crossings
    if order is None:
        order = best_scan_order(diagram.pd, tries=min(n, 12)) if n else []
    else:
        order = list(order)
    if any(type(i) is not int for i in order) or sorted(order) != list(range(n)):
        raise ValueError('order must be a permutation of every crossing')
    writhe = diagram.writhe()
    if modulus is None:
        # A^(5n) clears every denominator at every crossing, since at most
        # two circles close.  All stored coefficients have O(n log A) bits.
        a = value
        numerator = -(a**4 + 1)
        scale = 5 * n if n else 2
        target = (-1 if writhe % 2 else 1) * numerator * a**(scale + 3 * writhe - 2)
        weights = tuple(tuple(a**(6 - 2 * smoothing - 2 * closed) * numerator**closed
                              for closed in range(3)) for smoothing in (0, 1))
        empty_value = numerator
        result = {'modulus': None, 'A': a, 'writhe': writhe, 'scale_exponent': scale,
                  'loop_numerator': numerator, 'unknot_scaled_hex': hex(target),
                  'order': list(order)}
    else:
        a = value % modulus
        inv = pow(a, -1, modulus)
        delta = -(a * a + inv * inv) % modulus
        target = delta * pow((-a * a * a) % modulus, writhe, modulus) % modulus
        weights = tuple(tuple(weight * pow(delta, c, modulus) % modulus for c in range(3))
                        for weight in (a, inv))
        empty_value = delta
        result = {'modulus': modulus, 'A': a, 'writhe': writhe, 'delta': delta,
                  'unknot_residue': target, 'order': list(order)}
    state: dict[Pairing, int] = {(): 1}
    transitions, peak, width = 0, 1, 0
    reason = None
    if max_states is not None and max_states < 1:
        reason = 'state budget'
    for i in order:
        if reason:
            break
        _check(deadline)
        if max_transitions is not None and transitions + 2 * len(state) > max_transitions:
            reason = 'transition budget'
            break
        new: dict[Pairing, int] = {}
        for matching, coefficient in state.items():
            if transitions % 128 == 0:
                _check(deadline)
            for smoothing in (0, 1):
                target_matching, closed = attach(matching, diagram.pd[i], smoothing)
                if closed > 2:
                    raise ArithmeticError('a crossing closed more than two circles')
                term = coefficient * weights[smoothing][closed]
                residue = new.get(target_matching, 0) + term
                if modulus is not None:
                    residue %= modulus
                if residue:
                    new[target_matching] = residue
                else:
                    new.pop(target_matching, None)
                transitions += 1
                width = max(width, 2 * len(target_matching))
                peak = max(peak, len(new))
                if max_states is not None and len(new) > max_states:
                    reason = 'state budget'
                    break
            if reason:
                break
        if reason:
            break
        state = new
    result.update({'transitions': transitions, 'peak_states': peak, 'max_boundary': width,
                   'complete': reason is None})
    if reason:
        result.update({'detected': False, 'reason': reason})
    else:
        if any(m for m in state):
            raise ArithmeticError('bracket scan did not close')
        residue = empty_value if n == 0 else state.get((), 0)
        if modulus is None:
            result['scaled_bracket_hex'] = hex(residue)
        else:
            result['bracket_residue'] = residue
        result['detected'] = residue != target
    return result


def verify_obstruction(diagram: Diagram, evidence: dict[str, Any]) -> bool:
    """Recompute a modular witness; return False on malformed/tampered evidence.

    This is a deterministic verification computation, NOT a claim of a short
    NP certificate. A bracket witness may require exponential recomputation.
    """
    try:
        if evidence.get('kind') == 'modular-determinant':
            actual = determinant_obstruction(diagram)
            return (actual['detected'] and evidence.get('modulus') == actual['modulus']
                    and evidence.get('minor_residue') == actual['minor_residue'])
        if evidence.get('kind') in ('modular-bracket', 'integer-bracket'):
            actual = bracket_obstruction(diagram, order=evidence['order'],
                                         modulus=evidence['modulus'], value=evidence['A'])
            keys = (('scaled_bracket_hex', 'unknot_scaled_hex', 'writhe', 'scale_exponent',
                     'loop_numerator') if evidence['modulus'] is None else
                    ('bracket_residue', 'unknot_residue', 'writhe', 'delta'))
            return actual['detected'] and all(evidence.get(k) == actual[k] for k in keys)
        return False
    except (KeyError, TypeError, ValueError, ArithmeticError):
        return False
