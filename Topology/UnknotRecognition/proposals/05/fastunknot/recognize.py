"""An exact recognizer with one-sided modular filters and a complete backend.

Default extra bracket work is capped linearly in the number of crossings;
failure of a filter is never an UNKNOT verdict. The worst case remains exponential.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from math import isfinite
from time import monotonic
from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .filters import _check, bracket_obstruction, determinant_obstruction, verify_obstruction
from .scan import ScanLimit, best_scan_order, khovanov_rank
from .simplify import Move, apply_move, descending_start, simplify


@dataclass
class Result:
    status: str
    method: str
    input_crossings: int
    reduced_crossings: int
    seconds: float
    evidence: dict[str, Any] = field(default_factory=dict)

    @property
    def is_unknot(self) -> bool | None:
        return {'UNKNOT': True, 'KNOTTED': False}.get(self.status)

    def to_json(self) -> dict[str, Any]:
        return {
            'status': self.status, 'is_unknot': self.is_unknot, 'method': self.method,
            'input_crossings': self.input_crossings, 'reduced_crossings': self.reduced_crossings,
            'seconds': round(self.seconds, 6), 'evidence': self.evidence,
            'quasipolynomial_guarantee': False,
            'worst_case': 'exponential; no proved bound solely in scan width',
        }


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_alexander: bool = True, use_modular: bool = True, use_jones: bool = True,
              use_integer_jones: bool = True,
              jones_max_transitions: int | None = None, jones_max_states: int = 4096,
              max_objects: int | None = None, seconds: float | None = None,
              check_d_squared: bool = False) -> Result:
    """Recognize a knot, or return UNKNOWN if the complete computation is capped.

    --no-alexander disables both the modular determinant and the full polynomial.
    --no-jones disables the independent bracket filter. Object ceilings apply to
    the backend only: another method can still prove KNOTTED below that ceiling.
    Time limits are cooperative, not hard operating-system deadlines.
    """
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError('seconds must be finite and nonnegative')
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError('max_objects must be a positive integer')
    for name, limit in (('jones_max_transitions', jones_max_transitions),
                        ('jones_max_states', jones_max_states)):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError(name + ' must be a nonnegative integer')
    start = monotonic()
    deadline = None if seconds is None else start + seconds
    diagram = Diagram.from_pd(diagram.pd)  # also validate direct dataclass construction
    original = diagram
    evidence: dict[str, Any] = {}

    def finish(status: str, method: str) -> Result:
        return Result(status, method, original.crossings, diagram.crossings,
                      monotonic() - start, evidence)

    try:
        if diagram.crossings == 0:
            return finish('UNKNOT', 'reidemeister-reduction')
        _check(deadline)
        if use_reduction:
            diagram, trace = simplify(diagram)
            evidence['reidemeister_trace'] = [m.to_json() for m in trace]
        if diagram.crossings == 0:
            return finish('UNKNOT', 'reidemeister-reduction')
        _check(deadline)
        if use_descending:
            dart = descending_start(diagram)
            if dart is not None:
                evidence['descending_start_dart'] = dart
                return finish('UNKNOT', 'descending-diagram')
        _check(deadline)
        if use_alexander and use_modular:
            obstruction = determinant_obstruction(diagram, deadline=deadline)
            evidence['modular_determinant'] = obstruction
            if obstruction['detected']:
                evidence['obstruction'] = {'kind': 'modular-determinant', **obstruction}
                return finish('KNOTTED', 'modular-determinant')
        order = None
        if use_jones:
            order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
            limit = (10_000 + 200 * diagram.crossings if jones_max_transitions is None
                     else jones_max_transitions)
            obstruction = bracket_obstruction(diagram, order=order, max_transitions=limit,
                                               max_states=jones_max_states, deadline=deadline)
            evidence['modular_bracket'] = obstruction
            if obstruction['detected']:
                evidence['obstruction'] = {'kind': 'modular-bracket', **obstruction}
                return finish('KNOTTED', 'modular-bracket')
            if use_integer_jones and obstruction['complete']:
                exact = bracket_obstruction(diagram, order=order, modulus=None,
                                            max_transitions=limit, max_states=jones_max_states,
                                            deadline=deadline)
                evidence['integer_bracket'] = exact
                if exact['detected']:
                    evidence['obstruction'] = {'kind': 'integer-bracket', **exact}
                    return finish('KNOTTED', 'integer-bracket')
        _check(deadline)
        if use_alexander:
            poly = alexander_polynomial(diagram, deadline=deadline)
            evidence['alexander_polynomial'] = format_polynomial(poly)
            evidence['determinant'] = abs(evaluate(poly, -1))
            if poly != [1]:
                return finish('KNOTTED', 'alexander-polynomial')
        _check(deadline)
        remaining = None if deadline is None else max(0.0, deadline - monotonic())
        kh = khovanov_rank(diagram.pd, order=order, max_objects=max_objects,
                           seconds=remaining, check_d_squared=check_d_squared)
        evidence['khovanov'] = {'field': 'F2', 'unreduced_rank': kh['rank'],
                                'reduced_rank': kh['reduced_rank'],
                                'unreduced_rank_by_cube_degree': kh['by_degree'],
                                'scan_stats': kh['stats'], 'scan_order': kh['order']}
        return finish('UNKNOT' if kh['reduced_rank'] == 1 else 'KNOTTED',
                      'reduced-khovanov-F2-scan')
    except (ScanLimit, MemoryError) as exc:
        evidence['reason'] = str(exc) or 'memory allocation failed'
        return finish('UNKNOWN', 'resource-limit')


def verify_modular_result(diagram: Diagram, result: dict[str, Any]) -> bool:
    """Replay reductions and recompute a KNOTTED modular result on the input.

    It does not verify arbitrary Khovanov results or claim a small certificate.
    Unknown, malformed and tampered records fail closed.
    """
    try:
        diagram = Diagram.from_pd(diagram.pd)
        if result.get('status') != 'KNOTTED' or result.get('input_crossings') != diagram.crossings:
            return False
        evidence = result['evidence']
        for move in evidence.get('reidemeister_trace', []):
            diagram = apply_move(diagram, Move(move['kind'], tuple(move['crossings'])))
        if result.get('reduced_crossings') != diagram.crossings:
            return False
        return verify_obstruction(diagram, evidence['obstruction'])
    except (KeyError, TypeError, ValueError, ArithmeticError, AttributeError):
        return False
