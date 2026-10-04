"""A bounded exact modular Jones obstruction, never an unknot test.

We evaluate the Kauffman bracket at A=2 in F_1000000007. All arithmetic
is exact. A value different from 1 certifies knottedness; equality, or a
state-budget overflow, proves nothing. The complete scan is the fallback.
"""
from __future__ import annotations
from time import monotonic
from typing import Any
from .diagram import Diagram
from .optimized_algebra import glue
from .reference_algebra import ScanLimit

PRIME = 1_000_000_007
A_VALUE = 2


def normalized_bracket_mod(diagram: Diagram, *, order: list[int] | None = None,
                           max_states: int | None = 4096,
                           deadline: float | None = None) -> dict[str, Any]:
    """Return the exact modular value, or ``completed=False`` on state overflow.

    With max_states=B the filter takes polynomially bounded work in n and B.
    The field and evaluation point are fixed intentionally; no randomized
    soundness claim, primality assumption, or user-supplied modulus is needed.
    """
    from .ordering import best_scan_order, validate_order
    if max_states is not None and (type(max_states) is not int or max_states < 1):
        raise ValueError("max_states must be a positive integer or None")
    n = diagram.crossings
    order = best_scan_order(diagram.pd, tries=min(n, 12), deadline=deadline) if order is None \
        else validate_order(n, order)
    p, a = PRIME, A_VALUE
    ai = pow(a, -1, p)
    delta = -(a * a + ai * ai) % p
    states = {frozenset(): 1}
    points = frozenset()
    peak = 1
    width = 0
    transitions = 0
    for index in order:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted during Jones filter")
        glue.cache_clear()
        slots = diagram.pd[index]
        out = {}
        next_points = None
        for matching, value in states.items():
            if deadline is not None and monotonic() >= deadline:
                raise ScanLimit("time budget exhausted during Jones filter")
            for smoothing, coefficient in ((0, a), (1, ai)):
                g = glue(matching, smoothing, points, slots)
                next_points = g.points
                v = value * coefficient * pow(delta, g.closed, p)
                new = (out.get(g.matching, 0) + v) % p
                if new:
                    out[g.matching] = new
                else:
                    out.pop(g.matching, None)
                transitions += 1
                if max_states is not None and len(out) > max_states:
                    return {"completed": False, "reason": "state budget exhausted",
                            "prime": p, "A": a, "max_states": max_states,
                            "peak_states": len(out), "transitions": transitions,
                            "order": order}
        # The entire partial skein element can vanish modulo p; then the final
        # value is zero, independently of the remaining crossings.
        if not out:
            return {"completed": True, "prime": p, "A": a, "value": 0,
                    "writhe": diagram.writhe(), "peak_states": peak,
                    "max_boundary": width, "transitions": transitions,
                    "order": order, "early_zero": True}
        states = out
        points = next_points
        width = max(width, len(points))
        peak = max(peak, len(states))
    if points:
        raise ArithmeticError("Jones scan did not close")
    # The loop convention is Z(D)=delta*<D>, whereas <circle>=1.
    raw = states.get(frozenset(), 0) if n else delta
    writhe = diagram.writhe()
    value = raw * pow(delta, -1, p) * pow((-a**3) % p, -writhe, p) % p
    return {"completed": True, "prime": p, "A": a, "value": value,
            "writhe": writhe, "peak_states": peak, "max_boundary": width,
            "transitions": transitions, "order": order}
