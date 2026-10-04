"""One-sided finite-ring obstructions; equality NEVER certifies the unknot.

The modulus need not be prime for bracket evaluation, only A must be a unit.
The modular Alexander implementation uses the fixed prime 1_000_000_007.
All arithmetic is integral/modular; no floating-point tests are used.
"""
from __future__ import annotations

from collections import defaultdict
from time import monotonic
from typing import Callable
from .diagram import Diagram, DisjointSet
from .scan import ScanLimit, best_scan_order, glue

PRIME = 1_000_000_007


class FilterLimit(ScanLimit):
    """Only this optional filter exceeded its state cap; continue the recognizer."""


def _check(deadline: float | None) -> None:
    if deadline is not None and monotonic() > deadline:
        raise ScanLimit('time budget exhausted')


def determinant_mod(matrix: list[list[int]], prime: int = PRIME,
                    deadline: float | None = None) -> int:
    """Gaussian determinant over the fixed prime field (copying the input)."""
    if prime != PRIME:
        raise ValueError(f'this routine supports the verified prime {PRIME} only')
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError('matrix must be square')
    a = [[v % prime for v in row] for row in matrix]
    result = 1
    for j in range(n):
        _check(deadline)
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        value = a[j][j]
        result = result * value % prime
        reciprocal = pow(value, -1, prime)
        row = a[j]
        for i in range(j + 1, n):
            if not a[i][j]:
                continue
            factor = a[i][j] * reciprocal % prime
            target = a[i]
            for k in range(j + 1, n):
                target[k] = (target[k] - factor * row[k]) % prime
            target[j] = 0
    return result % prime


def _alexander_minor(diagram: Diagram, value: int, prime: int) -> list[list[int]]:
    """Wirtinger minor evaluated without building polynomial coefficient lists."""
    n = diagram.crossings
    arcs = DisjointSet(2 * n)
    for _, b, _, d in diagram.pd:
        arcs.union(b, d)
    roots = sorted({arcs.find(e) for e in range(2 * n)})
    column = {root: i for i, root in enumerate(roots)}
    incoming = {d // 4: d % 4 for d in diagram.traversal() if d % 2}
    matrix = [[0] * (n - 1) for _ in range(n - 1)]
    for i, (a, b, c, _) in enumerate(diagram.pd[:-1]):
        o, u, v = (column[arcs.find(e)] for e in (b, a, c))
        # u is the fixed a-port, not necessarily the globally incoming under-port.
        entries = ((o, 1 - value), (u, value), (v, -1)) if incoming[i] == 3 else \
                  ((o, 1 - value), (u, -1), (v, value))
        for col, coefficient in entries:
            if col < n - 1:
                matrix[i][col] = (matrix[i][col] + coefficient) % prime
    return matrix


def modular_alexander(diagram: Diagram, deadline: float | None = None) -> dict:
    """Reject nonunit Alexander polynomials using two exact necessary conditions.

    For a unit minor D(t)=+-t^k, D(-1) is +-1 and D(a)D(a^-1)=1.
    A modular mismatch is a proof of nontriviality; a match is inconclusive.
    """
    if diagram.crossings == 0:
        return {'obstruction': False, 'modulus': PRIME, 'checks': []}
    p = PRIME
    d = determinant_mod(_alexander_minor(diagram, -1, p), deadline=deadline)
    checks = [{'point': p - 1, 'value': d, 'allowed': [1, p - 1]}]
    if d not in (1, p - 1):
        return {'obstruction': True, 'modulus': p, 'checks': checks}
    a = 2
    ai = pow(a, -1, p)
    x = determinant_mod(_alexander_minor(diagram, a, p), deadline=deadline)
    y = determinant_mod(_alexander_minor(diagram, ai, p), deadline=deadline)
    checks.append({'point': a, 'reciprocal_point': ai, 'value': x,
                   'reciprocal_value': y, 'product': x * y % p, 'required_product': 1})
    return {'obstruction': x * y % p != 1, 'modulus': p, 'checks': checks}


def bracket_evaluation(diagram: Diagram, *, modulus: int = PRIME, a: int = 2,
                       order: list[int] | None = None, max_states: int | None = None,
                       deadline: float | None = None) -> dict:
    """Loop-inclusive Kauffman bracket via a matching-state dynamic program.

    Smoothing 0 has coefficient A and smoothing 1 coefficient A^-1.  The input
    PD convention gives normalized value (-A^3)^(-w) B(D).  The unknot value is
    delta=-A^2-A^-2.  The one-crossing calibration is tested independently.
    """
    if type(modulus) is not int or modulus < 2:
        raise ValueError('modulus must be an integer at least two')
    if type(a) is not int:
        raise ValueError('a must be an integer')
    try:
        ai = pow(a, -1, modulus)
    except ValueError as exc:
        raise ValueError('a must be invertible modulo modulus') from exc
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError('max_states must be a positive integer')
    n = diagram.crossings
    if order is None:
        _check(deadline)
        order = best_scan_order(diagram.pd, tries=min(n, 12)) if n else []
    elif (len(order) != n or any(type(i) is not int for i in order)
          or sorted(order) != list(range(n))):
        raise ValueError('order must be a permutation of the crossing indices')
    delta = (-a * a - ai * ai) % modulus
    if not n:
        return {'obstruction': False, 'modulus': modulus, 'a': a % modulus,
                'value': delta, 'unknot_value': delta, 'max_states': 1,
                'max_boundary': 0, 'order': []}
    states = {frozenset(): 1}
    points = frozenset()
    peak = 1
    width = 0
    for crossing in order:
        _check(deadline)
        slots = tuple(diagram.pd[crossing])
        new = {}
        for step, (matching, coefficient) in enumerate(states.items()):
            if step % 64 == 0:
                _check(deadline)
            for resolution, factor in ((0, a), (1, ai)):
                g = glue(matching, resolution, points, slots)
                value = coefficient * factor * pow(delta, g.closed, modulus)
                total = (new.get(g.matching, 0) + value) % modulus
                if total:
                    new[g.matching] = total
                else:
                    new.pop(g.matching, None)
                peak = max(peak, len(new))
                if max_states is not None and len(new) > max_states:
                    raise FilterLimit(f'Jones filter exceeded {max_states} live states')
        for edge in slots:
            points = points ^ {edge}
        states = new
        peak = max(peak, len(new))
        width = max(width, len(points))
    if points or any(matching for matching in states):
        raise ArithmeticError('bracket scan did not close')
    bracket = states.get(frozenset(), 0)
    value = bracket * pow((-pow(a, 3, modulus)) % modulus, -diagram.writhe(), modulus) % modulus
    return {'obstruction': value != delta, 'modulus': modulus, 'a': a % modulus,
            'value': value, 'unknot_value': delta, 'bracket': bracket,
            'writhe': diagram.writhe(), 'max_states': peak,
            'max_boundary': width, 'order': list(order)}
