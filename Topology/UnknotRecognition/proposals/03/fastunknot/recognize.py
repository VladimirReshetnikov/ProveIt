"""Exact recognition with bounded one-sided obstructions and a complete fallback."""
from __future__ import annotations
from dataclasses import dataclass, field
from time import monotonic
from typing import Any
from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .jones import FilterLimit, jones_obstruction
from .modular import alexander_obstruction
from .scan import ScanLimit, khovanov_rank
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

    def to_json(self):
        return {'status': self.status, 'is_unknot': self.is_unknot, 'method': self.method,
                'input_crossings': self.input_crossings, 'reduced_crossings': self.reduced_crossings,
                'seconds': round(self.seconds, 6), 'evidence': self.evidence,
                'quasipolynomial_guarantee': False,
                'worst_case': '2^O(n); no width-only bound on Khovanov multiplicity is claimed'}


def recognize(diagram: Diagram, *, use_reduction=True, use_descending=True,
              use_alexander=True, use_jones=True, use_modular=True,
              use_factorization=True, jones_max_states=2048,
              jones_max_transitions=50000, max_objects=None,
              seconds=None, check_d_squared=False, pivot='markowitz') -> Result:
    """Decide a validated knot. Resource exhaustion returns UNKNOWN, never KNOTTED.

    A Jones-only budget exhaustion skips that filter; global time/memory exhaustion
    returns UNKNOWN. With all ceilings removed, the Khovanov fallback is complete.
    """
    if seconds is not None and seconds < 0:
        raise ValueError('seconds must be nonnegative')
    if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
        raise ValueError('max_objects must be a nonnegative integer')
    if pivot not in ('markowitz', 'lifo'):
        raise ValueError('invalid pivot policy')
    start = monotonic()
    deadline = None if seconds is None else start + seconds
    original, evidence = diagram, {}
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit('time budget exhausted')
    def done(status, method):
        return Result(status, method, original.crossings, diagram.crossings,
                      monotonic() - start, evidence)
    try:
        check()
        if use_reduction:
            diagram, trace = simplify(diagram, check=check)
            evidence['reidemeister_trace'] = [move.to_json() for move in trace]
        if not diagram.crossings:
            return done('UNKNOT', 'reidemeister-reduction')
        if use_descending:
            dart = descending_start(diagram, check=check)
            if dart is not None:
                evidence['descending_start_dart'] = dart
                return done('UNKNOT', 'descending-diagram')
        if use_alexander and use_modular:
            evidence['alexander_modular'] = alexander_obstruction(diagram, check=check)
            if evidence['alexander_modular']['obstruction']:
                return done('KNOTTED', 'alexander-mod-prime')
        if use_jones:
            try:
                witness = jones_obstruction(diagram, max_states=jones_max_states,
                                             max_transitions=jones_max_transitions, check=check)
                evidence['jones'] = witness
                if witness['obstruction']:
                    # Witness pertains to this reduced diagram, not the input PD.
                    evidence['jones_diagram'] = diagram.to_json()
                    return done('KNOTTED', 'jones-mod-prime')
            except FilterLimit as exc:
                evidence['jones_skipped'] = str(exc)
        if use_alexander:
            check()
            poly = alexander_polynomial(diagram, check=check)
            evidence['alexander_polynomial'] = format_polynomial(poly)
            evidence['determinant'] = abs(evaluate(poly, -1))
            if poly != [1]:
                return done('KNOTTED', 'alexander-polynomial')
        check()
        remaining = None if deadline is None else max(0., deadline - monotonic())
        kh = khovanov_rank(diagram.pd, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared, pivot=pivot, factor=use_factorization)
        evidence['khovanov'] = {'field': 'F2', 'unreduced_rank': kh['rank'],
            'reduced_rank': kh['reduced_rank'], 'unreduced_rank_by_cube_degree': kh['by_degree'],
            'scan_stats': kh['stats'], 'scan_order': kh['order'],
            'factorized': kh.get('factorized', False)}
        if kh.get('factorized'):
            evidence['khovanov']['factor_results'] = kh['factor_results']
            evidence['khovanov']['decomposition'] = kh['decomposition']
        return done('UNKNOT' if kh['reduced_rank'] == 1 else 'KNOTTED',
                    'reduced-khovanov-F2-scan')
    except (ScanLimit, MemoryError) as exc:
        evidence['reason'] = str(exc) or 'memory allocation failed'
        return done('UNKNOWN', 'resource-limit')
