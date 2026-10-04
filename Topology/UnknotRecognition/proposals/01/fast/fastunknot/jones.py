"""Exact, one-sided Jones evaluations by frontier matching dynamic programming.

No homological generators or differential matrices are built. Coefficients of
all partial resolutions with the same boundary matching are added in F_p.
A nonunit normalized bracket evaluation certifies KNOTTED; equality is only
inconclusive. This module never certifies UNKNOT.
"""
from __future__ import annotations

from .diagram import Diagram
from .modular import PRIME
from .ordering import best_scan_order, validate_order
from .scan import glue


class JonesLimit(RuntimeError):
    """The optional filter exhausted its state budget; use the next stage."""


def jones_evaluations(diagram: Diagram, *, values=(2, 3), order=None,
                      max_states=None, check=None):
    """Evaluate delta^{-1} (-A^3)^{-w} sum_s A^(n-2|s|) delta^c(s).

    The convention is smoothing 0=(a,b)(c,d), smoothing 1=(a,d)(b,c),
    and the writhe is computed from both oriented branches at a crossing.
    Field arithmetic uses only the fixed known prime PRIME.
    """
    values = tuple(values)
    if not values or any(type(v) is not int or not 0 < v < PRIME for v in values):
        raise ValueError("evaluation points must be nonzero residues modulo PRIME")
    if max_states is not None and (type(max_states) is not int or max_states < 0):
        raise ValueError("max_states must be a nonnegative integer")
    if check is not None:
        check()
    p = PRIME
    inverses = tuple(pow(a, -1, p) for a in values)
    deltas = tuple((-a*a - inv*inv) % p for a, inv in zip(values, inverses))
    if 0 in deltas:
        raise ValueError("delta vanishes at an evaluation point")
    pd = diagram.pd
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12), check=check) if pd else []
    else:
        order = validate_order(len(pd), order)
    width = peak = transitions = 0
    if not pd:
        raw = deltas
    else:
        points = frozenset()
        states = {frozenset(): (1,) * len(values)}
        peak = 1
        for index in order:
            if check is not None:
                check()
            new = {}
            next_points = None
            slots = pd[index]
            for count, (matching, coefficient) in enumerate(states.items()):
                if check is not None and count % 64 == 0:
                    check()
                for smoothing in (0, 1):
                    glued = glue(matching, smoothing, points, slots)
                    next_points = glued.points
                    weights = values if smoothing == 0 else inverses
                    term = tuple(c * a * pow(delta, glued.closed, p) % p
                                 for c, a, delta in zip(coefficient, weights, deltas))
                    old = new.get(glued.matching)
                    if old is not None:
                        term = tuple((a + b) % p for a, b in zip(old, term))
                    if any(term):
                        new[glued.matching] = term
                    else:
                        new.pop(glued.matching, None)
                    transitions += 1
                    if max_states is not None and len(new) > max_states:
                        raise JonesLimit(f"Jones filter exceeded {max_states} frontier states")
            # An identically zero table stays zero under every remaining linear map.
            if not new:
                raw = (0,) * len(values)
                break
            states = new
            points = next_points
            width = max(width, len(points))
            peak = max(peak, len(states))
        else:
            if points:
                raise ArithmeticError("Jones scan ended with a nonempty boundary")
            raw = states.get(frozenset(), (0,) * len(values))
    writhe = diagram.writhe()
    normalized = []
    expected = []
    for a, delta, bracket in zip(values, deltas, raw):
        framing = pow((-pow(a, 3, p)) % p, writhe, p)
        unknot = delta * framing % p
        expected.append(unknot)
        normalized.append(bracket * pow(unknot, -1, p) % p)
    return {"prime": p, "A": list(values), "bracket": list(raw),
            "unknot_bracket": expected, "normalized": normalized, "writhe": writhe,
            "order": order, "stats": {"max_states": peak, "max_boundary": width,
                                        "transitions": transitions}}


def witness_from_evaluations(result):
    for i, value in enumerate(result['normalized']):
        if value != 1:
            return {"kind": "jones-nontrivial-evaluation", "prime": result['prime'],
                    "A": result['A'][i], "bracket": result['bracket'][i],
                    "unknot_bracket": result['unknot_bracket'][i],
                    "normalized": value, "writhe": result['writhe']}
    return None


def verify_jones_witness(diagram: Diagram, witness: dict) -> bool:
    """Recompute an exact modular witness. No Monte Carlo acceptance is used."""
    try:
        if (witness.get('kind') != 'jones-nontrivial-evaluation'
                or witness['prime'] != PRIME or witness['A'] not in (2, 3)):
            return False
        result = jones_evaluations(diagram, values=(witness['A'],))
        return witness_from_evaluations(result) == witness
    except (KeyError, TypeError, ValueError, ArithmeticError, AttributeError, IndexError):
        return False
