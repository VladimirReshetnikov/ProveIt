"""Exact modular Jones obstruction using a scalar frontier state sum.

A value != 1 proves KNOTTED. A value == 1 is INCONCLUSIVE, never UNKNOT.
The modulus need not be prime: only A and delta must be units.
This implementation deliberately does not use the Khovanov cobordism engine.
"""
from __future__ import annotations

from time import monotonic
from .diagram import Diagram
from .scan import ScanLimit, best_scan_order

Pairing = tuple[tuple[int, int], ...]
SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))


class JonesLimit(ScanLimit):
    """An optional filter's work cap was reached; fall back to the exact scanner."""


def _transition(pairing: Pairing, row: tuple, smoothing: int,
                new_boundary: set[int]) -> tuple[Pairing, int]:
    parent: dict[int, int] = {}
    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(x, y):
        parent[find(x)] = find(y)
    for a, b in pairing:
        union(a, b)
    for i, j in SMOOTHINGS[smoothing]:
        union(row[i], row[j])
    components = {find(x): [] for x in parent}
    for x in new_boundary:
        components[find(x)].append(x)
    result, closed = [], 0
    for endpoints in components.values():
        if not endpoints:
            closed += 1
        elif len(endpoints) == 2:
            result.append(tuple(sorted(endpoints)))
        else:
            raise ArithmeticError("frontier component has neither zero nor two ends")
    return tuple(sorted(result)), closed


def jones_modular(diagram: Diagram, *, modulus: int = 1_000_000_007,
                  A: int = 2, order: list[int] | None = None,
                  max_states: int | None = 100_000,
                  max_transitions: int | None = 200_000,
                  deadline: float | None = None) -> dict:
    """Evaluate (-A^3)^(-w) <D> modulo modulus, with <circle> = 1.

    The state sum temporarily uses <k circles> = delta^k, then divides by
    delta once. Deadlines are absolute monotonic times, shared with a pipeline.
    Optional caps limit *this filter*, not the fallback recognizer.
    """
    if type(modulus) is not int or modulus < 2 or type(A) is not int:
        raise ValueError("modulus >= 2 and A must be integers")
    for value in (max_states, max_transitions):
        if value is not None and (type(value) is not int or value < 1):
            raise ValueError("Jones caps must be positive integers or None")
    A %= modulus
    try:
        inv_A = pow(A, -1, modulus)
        delta = -(A * A + inv_A * inv_A) % modulus
        inv_delta = pow(delta, -1, modulus)
    except ValueError as exc:
        raise ValueError("A and delta = -A^2-A^-2 must be invertible") from exc
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted during Jones evaluation")
    check()
    n = diagram.crossings
    if order is not None:
        order = list(order)
        if any(type(i) is not int for i in order) or sorted(order) != list(range(n)):
            raise ValueError("order must be a permutation of all crossing indices")
    else:
        order = best_scan_order(diagram.pd, tries=min(n, 12)) if n else []
    check()
    states: dict[Pairing, int] = {(): 1}
    boundary: set[int] = set()
    peak, work, width = 1, 0, 0
    for crossing in order:
        row = diagram.pd[crossing]
        for label in row:
            boundary.symmetric_difference_update({label})
        width = max(width, len(boundary))
        new: dict[Pairing, int] = {}
        for pairing, coefficient in states.items():
            check()
            for smoothing, factor in ((0, A), (1, inv_A)):
                work += 1
                if max_transitions is not None and work > max_transitions:
                    raise JonesLimit("Jones transition cap exceeded")
                target, loops = _transition(pairing, row, smoothing, boundary)
                value = coefficient * factor * pow(delta, loops, modulus)
                new[target] = (new.get(target, 0) + value) % modulus
                if max_states is not None and len(new) > max_states:
                    raise JonesLimit("Jones state cap exceeded")
        peak = max(peak, len(new))
        states = {state: value for state, value in new.items() if value}
    check()
    if boundary or any(state for state in states):
        raise ArithmeticError("Jones frontier did not close")
    writhe = diagram.writhe()
    bracket = states.get((), 0) * inv_delta % modulus if n else 1
    value = bracket * pow(-pow(A, 3, modulus) % modulus, -writhe, modulus) % modulus
    return {"modulus": modulus, "A": A, "delta": delta, "writhe": writhe,
            "value": value, "unknot_value": 1, "proves_knotted": value != 1,
            "order": order, "max_states": peak, "transitions": work,
            "max_boundary": width}


def verify_jones_witness(diagram: Diagram, witness: dict) -> bool:
    """Recompute the finite-ring obstruction, without trusting supplied residues.

    This is a reproducibility checker, not a succinct polynomial-time proof
    checker. On untrusted large certificates the caller should use process limits.
    """
    try:
        answer = jones_modular(diagram, modulus=witness['modulus'], A=witness['A'],
                               order=witness['order'], max_states=None,
                               max_transitions=None)
        return answer['proves_knotted'] and all(
            answer[key] == witness.get(key) for key in
            ('modulus', 'A', 'delta', 'writhe', 'value', 'unknot_value'))
    except (ValueError, TypeError, KeyError, ArithmeticError):
        return False
