"""Exact accelerated recognizer; exponential unrestricted worst case.

Topological reductions -> visible connected sums -> bounded Jones obstruction
-> Alexander polynomial -> accelerated exact Khovanov scanner.

Every mathematical verdict is exact. Failure or collision of a filter is
inconclusive. A configured resource limit produces UNKNOWN, never KNOTTED.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from math import isfinite
from time import monotonic
from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .factor import decompose
from .jones import JonesLimit, jones_modular
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

    def to_json(self) -> dict[str, Any]:
        return {"status": self.status, "is_unknot": self.is_unknot,
                "method": self.method, "input_crossings": self.input_crossings,
                "reduced_crossings": self.reduced_crossings,
                "seconds": round(self.seconds, 6), "evidence": self.evidence,
                "quasipolynomial_guarantee": False,
                "worst_case": "2^O(n); with visible factor size m: poly(n) + n*2^O(m)"}


def recognize(diagram: Diagram, *, use_reduction: bool = True,
              use_descending: bool = True, use_alexander: bool = True,
              use_jones: bool = True, use_factorization: bool = True,
              max_objects: int | None = None, seconds: float | None = None,
              check_d_squared: bool = False, jones_max_states: int | None = 100_000,
              jones_max_transitions: int | None = 200_000,
              pivot_strategy: str = 'fill') -> Result:
    """Decide a validated classical knot; time limits are cooperative, not hard.

    max_objects limits ONLY the scanner; an independent filter can still decide
    the knot. Disable Jones with use_jones=False to force scanner-limit tests.
    The initial diagram must be built with Diagram.from_pd/from_json/etc.
    """
    if seconds is not None and (not isinstance(seconds, (int, float)) or
                                not isfinite(seconds) or seconds < 0):
        raise ValueError('seconds must be finite and nonnegative')
    for cap in (max_objects, jones_max_states, jones_max_transitions):
        if cap is not None and (type(cap) is not int or cap < 1):
            raise ValueError('resource caps must be positive integers or None')
    if pivot_strategy not in ('fill', 'lifo'):
        raise ValueError('pivot_strategy must be fill or lifo')
    start = monotonic()
    deadline = None if seconds is None else start + seconds
    original = diagram
    evidence: dict[str, Any] = {}
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit('time budget exhausted')
    def finish(status, method):
        return Result(status, method, original.crossings, diagram.crossings,
                      monotonic() - start, evidence)
    def prepare(d):
        check()
        ev = {}
        if use_reduction:
            d, trace = simplify(d, deadline=deadline)
            ev['reidemeister_trace'] = [m.to_json() for m in trace]
        check()
        if not d.crossings:
            return d, ev, 'reidemeister-reduction'
        if use_descending:
            dart = descending_start(d, deadline=deadline)
            if dart is not None:
                ev['descending_start_dart'] = dart
                return d, ev, 'descending-diagram'
        return d, ev, None
    def leaf(d, ev):
        check()
        if use_jones:
            try:
                witness = jones_modular(d, max_states=jones_max_states,
                    max_transitions=jones_max_transitions, deadline=deadline)
                ev['jones'] = witness
                if witness['proves_knotted']:
                    return 'KNOTTED', 'jones-modular'
            except JonesLimit as exc:
                ev['jones_skipped'] = str(exc)
        check()
        if use_alexander:
            poly = alexander_polynomial(d, deadline=deadline)
            ev['alexander_polynomial'] = format_polynomial(poly)
            ev['determinant'] = abs(evaluate(poly, -1))
            if poly != [1]:
                return 'KNOTTED', 'alexander-polynomial'
        check()
        remaining = None if deadline is None else max(0, deadline - monotonic())
        answer = khovanov_rank(d.pd, max_objects=max_objects, seconds=remaining,
            check_d_squared=check_d_squared, pivot_strategy=pivot_strategy)
        ev['khovanov'] = {"field": "F2", "unreduced_rank": answer['rank'],
            "reduced_rank": answer['reduced_rank'],
            "unreduced_rank_by_cube_degree": answer['by_degree'],
            "scan_stats": answer['stats'], "scan_order": answer['order']}
        return ('UNKNOT' if answer['reduced_rank'] == 1 else 'KNOTTED',
                'reduced-khovanov-F2-scan')
    try:
        diagram, evidence, proof = prepare(diagram)
        if proof:
            return finish('UNKNOT', proof)
        leaves, cuts = decompose(diagram, deadline=deadline) if use_factorization else ([(0, diagram)], [])
        if not cuts:
            status, method = leaf(diagram, evidence)
            return finish(status, method)
        evidence['decomposition'] = {'cuts': cuts, 'factors': []}
        evidence['factor_crossings'] = [d.crossings for _, d in leaves]
        memo, unknown = {}, False
        # Small summands first: one nontrivial factor is enough, and there is
        # no need to build the exponentially large tensor product homology.
        for node, factor in sorted(leaves, key=lambda x: (x[1].crossings, x[0])):
            check()
            key = factor.pd
            if key in memo:
                ev, status, method = memo[key]
            else:
                reduced, ev, proof = prepare(factor)
                ev['reduced_crossings'] = reduced.crossings
                try:
                    status, method = ('UNKNOT', proof) if proof else leaf(reduced, ev)
                except ScanLimit as exc:
                    check()  # An expired global deadline stops, rather than continuing.
                    ev['reason'] = str(exc)
                    status, method = 'UNKNOWN', 'resource-limit'
                memo[key] = ev, status, method
            evidence['decomposition']['factors'].append(
                {'node': node, 'status': status, 'method': method, 'evidence': ev})
            if status == 'KNOTTED':
                return finish('KNOTTED', 'connected-sum')
            unknown |= status == 'UNKNOWN'
        return finish('UNKNOWN' if unknown else 'UNKNOT', 'connected-sum')
    except (ScanLimit, MemoryError) as exc:
        evidence['reason'] = str(exc) or 'memory allocation failed'
        return finish('UNKNOWN', 'resource-limit')
