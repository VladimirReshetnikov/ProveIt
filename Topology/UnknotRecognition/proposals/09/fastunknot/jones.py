"""Exact modular Jones obstruction by a frontier Kauffman-bracket state sum.

A residue different from the unknot residue proves KNOTTED. Equality proves
nothing: it is never used as an unknot verdict. The filter is optional and
bounded; homology handles an inconclusive or capped calculation.

The local transfer implementation is independent of scan.glue.
"""
from math import gcd, isfinite
from time import monotonic
from .ordering import best_scan_order, order_profile, validate_order

MODULUS = 1_000_000_007
SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))


class JonesLimit(RuntimeError):
    """Only the optional filter was stopped; this is NOT a knot verdict."""


def join_matching(matching, slots, smoothing):
    """Attach two smoothing arcs to a matching, returning (matching, loops)."""
    mate = {}
    for a, b in matching:
        mate[a], mate[b] = b, a
    closed = 0
    for i, j in SMOOTHINGS[smoothing]:
        a, b = slots[i], slots[j]
        if a == b:
            closed += 1
        elif a in mate and b in mate:
            u, v = mate.pop(a), mate.pop(b)
            if u == b:
                closed += 1
            else:
                mate[u], mate[v] = v, u
        elif a in mate:
            u = mate.pop(a)
            mate[u], mate[b] = b, u
        elif b in mate:
            v = mate.pop(b)
            mate[v], mate[a] = a, v
        else:
            mate[a], mate[b] = b, a
    return tuple(sorted((a, b) for a, b in mate.items() if a < b)), closed


def jones_residue(diagram, *, modulus=MODULUS, a=2, order=None,
                  max_states=8192, max_transitions=250000, deadline=None):
    """Compute V(A**-4) modulo modulus (a ring, not necessarily a field).

    A and delta must be units. This restriction avoids dividing by zero. Caps
    bound LIVE dictionary keys and smoothing transitions. A cap raises
    JonesLimit, which callers must treat as inconclusive, not as nontriviality.
    """
    if type(modulus) is not int or modulus < 3 or type(a) is not int:
        raise ValueError("modulus must be an integer >= 3 and a an integer")
    for limit in (max_states, max_transitions):
        if limit is not None and (type(limit) is not int or limit < 1):
            raise ValueError("Jones limits must be positive integers or None")
    if deadline is not None and not isfinite(deadline):
        raise ValueError("deadline must be finite")
    a %= modulus
    if gcd(a, modulus) != 1:
        raise ValueError("A must be invertible modulo the modulus")
    ai = pow(a, -1, modulus)
    delta = (-a*a - ai*ai) % modulus
    if gcd(delta, modulus) != 1:
        raise ValueError("the circle value must be invertible modulo the modulus")
    pd = diagram.pd
    n = len(pd)
    if deadline is not None and monotonic() >= deadline:
        raise JonesLimit("Jones time budget exhausted")
    order = (best_scan_order(pd, tries=min(n, 12)) if n else []) if order is None else validate_order(order, n)
    if not n:
        return {"residue": 1, "unknot_residue": 1, "obstructs": False,
                "modulus": modulus, "A": a, "order": [], "max_states": 1,
                "transitions": 0, "max_boundary": 0}
    states = {(): 1}
    peak = 1
    transitions = 0
    loop_factors = (1, delta, delta * delta % modulus)
    for index in order:
        if deadline is not None and monotonic() >= deadline:
            raise JonesLimit("Jones time budget exhausted")
        target = {}
        for matching, coefficient in states.items():
            for smoothing, weight in enumerate((a, ai)):
                transitions += 1
                if max_transitions is not None and transitions > max_transitions:
                    raise JonesLimit("Jones transition ceiling reached")
                if transitions % 256 == 0 and deadline is not None and monotonic() >= deadline:
                    raise JonesLimit("Jones time budget exhausted")
                new, loops = join_matching(matching, pd[index], smoothing)
                value = (target.get(new, 0) + coefficient * weight * loop_factors[loops]) % modulus
                if value:
                    target[new] = value
                else:
                    target.pop(new, None)
                peak = max(peak, len(target))
                if max_states is not None and len(target) > max_states:
                    raise JonesLimit("Jones state ceiling reached")
        states = target
    if any(key for key in states):
        raise ArithmeticError("Jones scan did not close")
    bracket = states.get((), 0)
    # With the package's PD convention the 0-smoothing has weight A.
    # The signed writhe is positive when over enters three slots after under.
    normalizer = pow((-a**3) % modulus, -diagram.writhe(), modulus)
    residue = bracket * pow(delta, -1, modulus) * normalizer % modulus
    return {"residue": residue, "unknot_residue": 1, "obstructs": residue != 1,
            "modulus": modulus, "A": a, "order": order, "max_states": peak,
            "transitions": transitions, "max_boundary": order_profile(pd, order)[0]}
