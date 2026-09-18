"""Exact, one-sided Jones obstruction by aggregating smoothing frontiers.

For our PD convention, smoothing 0 has coefficient A, smoothing 1 has A^-1.
The unnormalized bracket of the empty circle is delta=-A^2-A^-2. A diagram
of the unknot therefore has bracket delta*(-A^3)^writhe. We compare these
quantities in Z/modulus Z; a mismatch is a proof, not a probability statement.
Equality is INCONCLUSIVE, never a certificate of the unknot.

The dictionary carries only a perfect matching of open edges and a residue;
all partial smoothing states with the same matching are summed immediately.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import gcd, isfinite
from time import monotonic
from typing import Iterable

from .diagram import Diagram
from .scan import ScanLimit, SMOOTHINGS, best_scan_order, order_profile

Pairing = tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class Evaluation:
    modulus: int
    a: int
    bracket: int
    unknot_bracket: int
    writhe: int
    max_states: int
    width: int
    order: tuple[int, ...]

    @property
    def obstructs_unknot(self) -> bool:
        return self.bracket != self.unknot_bracket

    def to_json(self) -> dict:
        return {"modulus": self.modulus, "A": self.a, "bracket": self.bracket,
                "unknot_bracket": self.unknot_bracket, "writhe": self.writhe,
                "obstructs_unknot": self.obstructs_unknot,
                "max_states": self.max_states, "width": self.width,
                "order": list(self.order),
                "meaning_of_equality": "inconclusive"}


def transition(matching: Pairing, slots: tuple[int, ...], smoothing: int,
               new_boundary: frozenset[int]) -> tuple[Pairing, int]:
    """Glue one smoothing, tracing its paths with a small disjoint-set forest.

    Vertices here are edge midpoints, not crossings. A component with two
    new boundary ends is an arc; a component without ends is a closed circle.
    Handles self-loops and parallel edges without special smoothing cases.
    """
    parent = {x: x for pair in matching for x in pair}
    parent.update({x: x for x in slots if x not in parent})

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        x, y = find(x), find(y)
        if x != y:
            parent[x] = y

    for x, y in matching:
        union(x, y)
    for i, j in SMOOTHINGS[smoothing]:
        union(slots[i], slots[j])
    groups: dict[int, list[int]] = {}
    for x in parent:
        groups.setdefault(find(x), [])
    for x in new_boundary:
        groups[find(x)].append(x)
    pairs, closed = [], 0
    for ends in groups.values():
        if len(ends) == 2:
            pairs.append(tuple(sorted(ends)))
        elif not ends:
            closed += 1
        else:
            raise ArithmeticError("a smoothing component has neither zero nor two ends")
    return tuple(sorted(pairs)), closed


def bracket_evaluation(diagram: Diagram, *, a: int = 2, modulus: int = 1_000_000_007,
                       order: Iterable[int] | None = None,
                       max_states: int | None = 4096,
                       seconds: float | None = None) -> Evaluation:
    """Evaluate the Jones obstruction exactly, with cooperative resource limits.

    Primality of modulus is not required. Only A must be invertible. No
    modular division by delta is used, so even delta=0 is safe (but useless).
    """
    if type(modulus) is not int or modulus < 2 or type(a) is not int or gcd(a, modulus) != 1:
        raise ValueError("modulus >= 2 and an integer A coprime to it are required")
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError("max_states must be a positive integer or None")
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    deadline = None if seconds is None else monotonic() + seconds

    def check() -> None:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("Jones time budget exhausted")

    check()
    pd = diagram.pd
    if order is None:
        order = best_scan_order(list(pd), tries=min(len(pd), 12))
    else:
        order = list(order)
    if (any(type(i) is not int for i in order)
            or sorted(order) != list(range(len(pd)))):
        raise ValueError("order must be a permutation of all crossing indices")
    check()
    a %= modulus
    ai = pow(a, -1, modulus)
    delta = (-a * a - ai * ai) % modulus
    w = diagram.writhe()
    expected = delta * pow((-a**3) % modulus, w, modulus) % modulus
    if not pd:
        return Evaluation(modulus, a, delta, expected, w, 1, 0, tuple(order))
    states: dict[Pairing, int] = {(): 1}
    boundary: set[int] = set()
    peak = 1
    for index in order:
        check()
        slots = pd[index]
        for edge in slots:
            boundary.symmetric_difference_update((edge,))
        new_boundary = frozenset(boundary)
        nxt: dict[Pairing, int] = {}
        for count, (matching, coefficient) in enumerate(states.items()):
            if count % 64 == 0:
                check()
            for smoothing, factor in ((0, a), (1, ai)):
                new_matching, closed = transition(matching, slots, smoothing, new_boundary)
                value = (nxt.get(new_matching, 0)
                         + coefficient * factor * pow(delta, closed, modulus)) % modulus
                if value:
                    nxt[new_matching] = value
                else:
                    nxt.pop(new_matching, None)
                # Test during construction, not only after a large allocation.
                if max_states is not None and len(nxt) > max_states:
                    raise ScanLimit(f"Jones frontier exceeded {max_states} states")
                peak = max(peak, len(nxt))
        states = nxt
    check()
    if boundary or any(m for m in states):
        raise ArithmeticError("closed diagram has an open smoothing frontier")
    return Evaluation(modulus, a, states.get((), 0), expected, w, peak,
                      order_profile(list(pd), order)[0], tuple(order))


def verify_obstruction(diagram: Diagram, evidence: dict,
                       *, max_states: int | None = None,
                       seconds: float | None = None) -> bool:
    """Recompute an evaluation and compare all mathematical certificate fields.

    This is reproducible evidence, not a promise of a polynomial-size NP proof.
    Time and state limits raise ScanLimit; they never validate a certificate.
    """
    try:
        evaluation = bracket_evaluation(
            diagram, a=evidence['A'], modulus=evidence['modulus'],
            order=evidence['order'], max_states=max_states, seconds=seconds)
    except (KeyError, TypeError, ValueError):
        return False
    return (evaluation.obstructs_unknot
            and all(evidence.get(key) == value for key, value in
                    (("bracket", evaluation.bracket),
                     ("unknot_bracket", evaluation.unknot_bracket),
                     ("writhe", evaluation.writhe))))
