"""Exact portfolio recognizer with one-sided filters and a complete F2 fallback.

No quasi-polynomial bound is claimed.  An exhausted optional Jones state cap
falls through to the exact backend; an exhausted total budget returns UNKNOWN.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import math
from time import monotonic
from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .decompose import factor_diagram
from .filters import FilterLimit, bracket_evaluation, modular_alexander
from .scan import ScanLimit, best_scan_order, khovanov_rank
from .simplify import descending_start, simplify


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
        return {'status': self.status, 'is_unknot': self.is_unknot, 'method': self.method,
                'input_crossings': self.input_crossings,
                'reduced_crossings': self.reduced_crossings,
                'seconds': round(self.seconds, 6), 'evidence': self.evidence,
                'quasipolynomial_guarantee': False,
                'worst_case': '2^O(n) upper bound; no width-only bound for Khovanov multiplicities'}


def recognize(diagram: Diagram, *, use_reduction: bool = True,
              use_descending: bool = True, use_alexander: bool = True,
              use_modular: bool = True, use_jones: bool = True,
              use_factorization: bool = True, jones_max_states: int = 20000,
              max_objects: int | None = None, seconds: float | None = None,
              check_d_squared: bool = False) -> Result:
    """Decide unknotness. Disabling all limits leaves a complete exact algorithm.

    `use_alexander=False` disables both Alexander stages; `use_jones=False`
    separately disables the Jones filter. `max_objects` only bounds Khovanov
    complexes: a filter may still finish before that ceiling is relevant.
    """
    if seconds is not None and (not math.isfinite(seconds) or seconds < 0):
        raise ValueError('seconds must be finite and nonnegative')
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError('max_objects must be a positive integer')
    if type(jones_max_states) is not int or jones_max_states < 1:
        raise ValueError('jones_max_states must be a positive integer')
    start = monotonic()
    deadline = None if seconds is None else start + seconds
    original = diagram
    evidence: dict[str, Any] = {}

    def result(status: str, method: str) -> Result:
        return Result(status, method, original.crossings, diagram.crossings,
                      monotonic() - start, evidence)

    def check() -> None:
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit('time budget exhausted')

    def remaining() -> float | None:
        return None if deadline is None else max(0.0, deadline - monotonic())

    try:
        check()
        if use_reduction:
            diagram, trace = simplify(diagram, deadline=deadline)
            evidence['reidemeister_trace'] = [m.to_json() for m in trace]
        if not diagram.crossings:
            return result('UNKNOT', 'reidemeister-reduction')
        check()
        if use_descending:
            dart = descending_start(diagram)
            if dart is not None:
                evidence['descending_start_dart'] = dart
                return result('UNKNOT', 'descending-diagram')
        check()
        if use_factorization:
            factors, trace = factor_diagram(diagram, deadline)
            if len(factors) > 1:
                evidence['split_trace'] = trace
                evidence['factor_count'] = len(factors)
                evidence['factors'] = []
                unresolved = False
                for factor in factors:
                    child = recognize(factor, use_reduction=use_reduction,
                                      use_descending=use_descending, use_alexander=use_alexander,
                                      use_modular=use_modular, use_jones=use_jones,
                                      use_factorization=False, jones_max_states=jones_max_states,
                                      max_objects=max_objects, seconds=remaining(),
                                      check_d_squared=check_d_squared)
                    evidence['factors'].append({'pd': [list(c) for c in factor.pd],
                                                'result': child.to_json()})
                    if child.status == 'KNOTTED':
                        return result('KNOTTED', 'connected-sum')
                    unresolved |= child.status == 'UNKNOWN'
                return result('UNKNOWN' if unresolved else 'UNKNOT', 'connected-sum')
        check()
        if use_alexander and use_modular:
            modular = modular_alexander(diagram, deadline)
            evidence['alexander_modular'] = modular
            if modular['obstruction']:
                return result('KNOTTED', 'alexander-modular')
        check()
        order = None
        if use_jones:
            order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
            try:
                jones = bracket_evaluation(diagram, order=order, max_states=jones_max_states,
                                           deadline=deadline)
                evidence['jones_modular'] = jones
                if jones['obstruction']:
                    return result('KNOTTED', 'jones-modular')
            except FilterLimit as exc:
                evidence['jones_modular'] = {'skipped': str(exc)}
        check()
        if use_alexander:
            poly = alexander_polynomial(diagram, deadline=deadline)
            evidence['alexander_polynomial'] = format_polynomial(poly)
            evidence['determinant'] = abs(evaluate(poly, -1))
            if poly != [1]:
                return result('KNOTTED', 'alexander-polynomial')
        check()
        kh = khovanov_rank(diagram.pd, order=order, factor=False,
                           max_objects=max_objects, seconds=remaining(),
                           check_d_squared=check_d_squared)
        evidence['khovanov'] = {'field': 'F2', 'unreduced_rank': kh['rank'],
                                'reduced_rank': kh['reduced_rank'],
                                'unreduced_rank_by_cube_degree': kh['by_degree'],
                                'scan_stats': kh['stats'], 'scan_order': kh['order']}
        return result('UNKNOT' if kh['reduced_rank'] == 1 else 'KNOTTED',
                      'reduced-khovanov-F2-scan')
    except (ScanLimit, MemoryError) as exc:
        evidence['reason'] = str(exc) or 'memory allocation failed'
        return result('UNKNOWN', 'resource-limit')
