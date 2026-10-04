"""A one-sided Jones obstruction computed by scalar frontier contraction.

Only a mismatch proves KNOTTED. Equality never proves UNKNOT. Arithmetic is
exact in F_p; modular collisions and budget exhaustion merely skip this filter.
The complete Khovanov fallback is retained.
"""
from __future__ import annotations
from collections import defaultdict
from hashlib import sha256
import json
from typing import Callable

from .diagram import Diagram
from .ordering import best_scan_order, validate_order

PRIME = 2147483647  # 2^31 - 1, a prime.
A_VALUE = 2
SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))


class FilterLimit(RuntimeError):
    """A bounded optional obstruction stage was abandoned; this proves nothing."""


def _glue(matching, slots, smoothing, boundary):
    parent = {p: p for pair in matching for p in pair}
    parent.update({p: p for p in slots if p not in parent})
    def find(p):
        while parent[p] != p:
            parent[p] = parent[parent[p]]
            p = parent[p]
        return p
    for p, q in matching:
        parent[find(p)] = find(q)
    for a, b in SMOOTHINGS[smoothing]:
        parent[find(slots[a])] = find(slots[b])
    groups = {find(p): [] for p in parent}
    for p in boundary:
        groups[find(p)].append(p)
    closed, pairs = 0, []
    for ends in groups.values():
        if not ends:
            closed += 1
        elif len(ends) == 2:
            pairs.append(tuple(sorted(ends)))
        else:
            raise ArithmeticError("a bracket smoothing has neither zero nor two ends")
    return tuple(sorted(pairs)), closed


def pd_digest(diagram: Diagram) -> str:
    return sha256(json.dumps(diagram.to_json()['pd'], separators=(',', ':')).encode()).hexdigest()


def jones_obstruction(diagram: Diagram, *, order=None, max_states: int | None = 2048,
                      max_transitions: int | None = 50000,
                      check: Callable[[], None] = lambda: None) -> dict:
    """Return an exact finite-field evaluation and whether it differs from the unknot.

    Stored bracket B assigns delta to every closed circle (including the first).
    Our PD convention has B(D_unknot) = delta * (-A^3)^w for an unknot diagram.
    An explicit scan order must contain every crossing exactly once.
    """
    for name, limit in (("max_states", max_states), ("max_transitions", max_transitions)):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError(name + " must be a nonnegative integer")
    check()
    pd = diagram.pd
    order = (best_scan_order(pd, tries=min(len(pd), 12), check=check) if order is None
             else validate_order(len(pd), order))
    p, a = PRIME, A_VALUE
    inv_a = pow(a, -1, p)
    delta = (-a * a - inv_a * inv_a) % p
    states = {(): 1}
    boundary = set()
    peak, transitions = 1, 0
    for cid in order:
        check()
        slots = pd[cid]
        for edge in slots:
            boundary.symmetric_difference_update((edge,))
        new = {}
        for matching, coefficient in states.items():
            check()
            for smoothing, weight in ((0, a), (1, inv_a)):
                transitions += 1
                if max_transitions is not None and transitions > max_transitions:
                    raise FilterLimit("Jones transition budget exhausted")
                target, closed = _glue(matching, slots, smoothing, boundary)
                value = (new.get(target, 0) + coefficient * weight * pow(delta, closed, p)) % p
                if value:
                    new[target] = value
                else:
                    new.pop(target, None)
                if max_states is not None and len(new) > max_states:
                    raise FilterLimit("Jones frontier-state budget exhausted")
        states = new
        peak = max(peak, len(states))
    if boundary or any(m for m in states):
        raise ArithmeticError("Jones evaluation ended with an open boundary")
    writhe = diagram.writhe()
    bracket = states.get((), 0) if pd else delta
    expected = delta * pow((-a ** 3) % p, writhe, p) % p
    return {"obstruction": bracket != expected, "prime": p, "A": a,
            "writhe": writhe, "bracket": bracket, "unknot_bracket": expected,
            "normalized_jones": bracket * pow(expected, -1, p) % p,
            "pd_sha256": pd_digest(diagram), "order": order,
            "max_states": peak, "transitions": transitions}


def verify_obstruction(diagram: Diagram, witness: dict) -> bool:
    """Replay a finite-field witness. This recomputes the contraction, not an NP proof."""
    if not isinstance(witness, dict) or witness.get('prime') != PRIME or witness.get('A') != A_VALUE:
        return False
    if witness.get('pd_sha256') != pd_digest(diagram):
        return False
    try:
        result = jones_obstruction(diagram, order=witness['order'],
                                   max_states=None, max_transitions=None)
    except (ValueError, KeyError, TypeError):
        return False
    fields = ('writhe', 'bracket', 'unknot_bracket', 'pd_sha256')
    return result['obstruction'] and all(result[k] == witness.get(k) for k in fields)
