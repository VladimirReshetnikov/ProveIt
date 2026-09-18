"""Exact recognition with bounded Jones screening and compressed sum factors.

No global quasi-polynomial bound is claimed. Negative modular Jones evidence
is exact; equality always falls through. Without user resource ceilings the
Khovanov fallback makes the recognizer complete. Resource exhaustion produces
UNKNOWN, never a mathematical verdict.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from math import isfinite
from time import monotonic
from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .factor import decompose
from .jones import bracket_evaluation
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
        return {"UNKNOT": True, "KNOTTED": False}.get(self.status)

    def to_json(self) -> dict[str, Any]:
        return {"status": self.status, "is_unknot": self.is_unknot,
                "method": self.method, "input_crossings": self.input_crossings,
                "reduced_crossings": self.reduced_crossings,
                "seconds": round(self.seconds, 6), "evidence": self.evidence,
                "quasipolynomial_guarantee": False,
                "worst_case": "2^O(n); no width-only bound for Khovanov object multiplicities"}


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_alexander: bool = True, use_jones: bool = True, use_factor: bool = True,
              jones_max_states: int | None = 4096, max_objects: int | None = None,
              seconds: float | None = None, check_d_squared: bool = False) -> Result:
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    for value, name in ((max_objects, 'max_objects'), (jones_max_states, 'jones_max_states')):
        if value is not None and (type(value) is not int or value < 1):
            raise ValueError(f"{name} must be a positive integer or None")
    start = monotonic()
    deadline = None if seconds is None else start + seconds

    def check() -> None:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")

    def remaining() -> float | None:
        return None if deadline is None else max(0.0, deadline - monotonic())

    def analyze(original: Diagram, factorize: bool) -> Result:
        begun = monotonic()
        current = original
        evidence: dict[str, Any] = {}

        def done(status: str, method: str) -> Result:
            return Result(status, method, original.crossings, current.crossings,
                          monotonic() - begun, evidence)

        try:
            check()
            if use_reduction:
                current, trace = simplify(current, deadline=deadline)
                evidence['reidemeister_trace'] = [move.to_json() for move in trace]
            check()
            if current.crossings == 0:
                return done('UNKNOT', 'reidemeister-reduction')
            if use_descending:
                dart = descending_start(current)
                check()
                if dart is not None:
                    evidence['descending_start_dart'] = dart
                    return done('UNKNOT', 'descending-diagram')
            if factorize:
                factors, certificate = decompose(current, deadline=deadline)
                if len(factors) > 1:
                    evidence['decomposition'] = certificate
                    evidence['factor_results'] = []
                    unknown = False
                    for index, part in enumerate(factors):
                        result = analyze(part, False)
                        evidence['factor_results'].append(
                            {'factor_index': index, 'result': result.to_json()})
                        if result.status == 'KNOTTED':
                            return done('KNOTTED', 'connected-sum')
                        unknown |= result.status == 'UNKNOWN'
                        check()
                    return done('UNKNOWN' if unknown else 'UNKNOT', 'connected-sum')
            if use_jones:
                # The screen has its own STATE ceiling: hitting it skips the
                # screen, rather than preventing the complete fallback.
                try:
                    ev = bracket_evaluation(current, max_states=jones_max_states,
                                            seconds=remaining())
                    evidence['jones'] = ev.to_json()
                    if ev.obstructs_unknot:
                        return done('KNOTTED', 'jones-modular-frontier')
                except ScanLimit as exc:
                    evidence['jones_skipped'] = str(exc)
                    check()   # global time exhaustion is not a skipped screen
            check()
            if use_alexander:
                polynomial = alexander_polynomial(current, deadline=deadline)
                check()
                evidence['alexander_coefficients'] = polynomial
                evidence['alexander_polynomial'] = format_polynomial(polynomial)
                evidence['determinant'] = abs(evaluate(polynomial, -1))
                if polynomial != [1]:
                    return done('KNOTTED', 'alexander-polynomial')
            kh = khovanov_rank(current.pd, max_objects=max_objects, seconds=remaining(),
                               check_d_squared=check_d_squared)
            check()
            evidence['khovanov'] = {
                'field': 'F2', 'unreduced_rank': kh['rank'],
                'reduced_rank': kh['reduced_rank'],
                'unreduced_rank_by_cube_degree': kh['by_degree'],
                'scan_stats': kh['stats'], 'scan_order': kh['order']}
            return done('UNKNOT' if kh['reduced_rank'] == 1 else 'KNOTTED',
                        'reduced-khovanov-F2-scan')
        except (ScanLimit, MemoryError) as exc:
            evidence['reason'] = str(exc) or 'memory allocation failed'
            return done('UNKNOWN', 'resource-limit')

    result = analyze(diagram, use_factor)
    result.seconds = monotonic() - start
    return result
