"""Exact unknot recognition with cheap one-sided filters and a complete fallback.

General worst case: 2^O(n). No general quasi-polynomial bound is claimed.
Finite-field collisions are inconclusive, never evidence of unknottedness.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from time import monotonic
from typing import Any
import math

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .jones import JonesLimit, jones_evaluations, witness_from_evaluations
from .modular import alexander_witness
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
        return {
            "status": self.status, "is_unknot": self.is_unknot, "method": self.method,
            "input_crossings": self.input_crossings, "reduced_crossings": self.reduced_crossings,
            "seconds": round(self.seconds, 6), "evidence": self.evidence,
            "quasipolynomial_guarantee": False,
            "worst_case": "2^O(n) bit operations; no general bound solely in scan width",
        }


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_alexander: bool = True, use_modular: bool = True, use_jones: bool = True,
              factor_connected: bool = True, max_jones_states: int | None = 4096,
              max_objects: int | None = None, seconds: float | None = None,
              check_d_squared: bool = False, pivot: str = "markowitz") -> Result:
    start = monotonic()
    if seconds is not None and (type(seconds) not in (int, float)
                                or not math.isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    for name, limit in (("max_objects", max_objects), ("max_jones_states", max_jones_states)):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError(f"{name} must be a nonnegative integer")
    if pivot not in ("lifo", "markowitz"):
        raise ValueError("pivot must be lifo or markowitz")
    deadline = None if seconds is None else start + seconds
    original = diagram
    evidence: dict[str, Any] = {}
    phase = "validation"

    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted")

    def finish(status, method):
        return Result(status, method, original.crossings, diagram.crossings,
                      monotonic() - start, evidence)

    try:
        check()
        diagram = Diagram.from_pd(diagram.pd)
        if use_reduction:
            phase = "reidemeister-reduction"
            diagram, trace = simplify(diagram, check=check)
            evidence["reidemeister_trace"] = [move.to_json() for move in trace]
        check()
        if diagram.crossings == 0:
            return finish("UNKNOT", "reidemeister-reduction")
        if use_descending:
            phase = "descending-diagram"
            dart = descending_start(diagram)
            check()
            if dart is not None:
                evidence["descending_start_dart"] = dart
                return finish("UNKNOT", "descending-diagram")
        if use_alexander and use_modular:
            phase = "alexander-modular-evaluation"
            witness = alexander_witness(diagram, check=check)
            if witness is not None:
                evidence["witness"] = witness
                evidence["witness_diagram"] = diagram.to_json()
                return finish("KNOTTED", phase)
        if use_jones and max_jones_states != 0:
            phase = "jones-modular-evaluation"
            try:
                result = jones_evaluations(diagram, max_states=max_jones_states, check=check)
                evidence["jones"] = result
                witness = witness_from_evaluations(result)
                if witness is not None:
                    evidence["witness"] = witness
                    evidence["witness_diagram"] = diagram.to_json()
                    return finish("KNOTTED", phase)
            except JonesLimit as exc:
                evidence["jones_filter_skipped"] = str(exc)
        if use_alexander:
            phase = "alexander-polynomial"
            poly = alexander_polynomial(diagram, check=check)
            evidence["alexander_polynomial"] = format_polynomial(poly)
            evidence["determinant"] = abs(evaluate(poly, -1))
            if poly != [1]:
                return finish("KNOTTED", phase)
        phase = "reduced-khovanov-F2-scan"
        check()
        remaining = None if deadline is None else max(0.0, deadline - monotonic())
        kh = khovanov_rank(diagram.pd, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared, factor_connected=factor_connected,
                           pivot=pivot)
        evidence["khovanov"] = {
            "field": "F2", "unreduced_rank": kh["rank"], "reduced_rank": kh["reduced_rank"],
            "unreduced_rank_by_cube_degree": kh["by_degree"], "scan_stats": kh["stats"],
            "scan_order": kh["order"], "pivot_strategy": pivot,
        }
        if "factorization" in kh:
            evidence["khovanov"]["factorization"] = kh["factorization"]
            evidence["khovanov"]["factor_cuts"] = kh["factor_cuts"]
        return finish("UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED", phase)
    except (ScanLimit, MemoryError) as exc:
        evidence["reason"] = str(exc) or "memory allocation failed"
        evidence["phase"] = phase
        return finish("UNKNOWN", "resource-limit")


def verify_rejection(diagram: Diagram, result: Result | dict) -> bool:
    """Verify a modular rejection and the full reduction trace connecting it to input.

    This deliberately does not claim to verify arbitrary Khovanov transcripts.
    """
    from .jones import verify_jones_witness
    from .modular import verify_alexander_witness
    from .simplify import Move, apply_move
    if isinstance(result, Result):
        result = result.to_json()
    try:
        if result['status'] != 'KNOTTED':
            return False
        evidence = result['evidence']
        current = Diagram.from_pd(diagram.pd)
        for item in evidence.get('reidemeister_trace', []):
            current = apply_move(current, Move(item['kind'], tuple(item['crossings'])))
        if current != Diagram.from_json(evidence['witness_diagram']):
            return False
        witness = evidence['witness']
        kind = witness.get('kind')
        if kind == 'alexander-nonunit-evaluation':
            return verify_alexander_witness(current, witness)
        if kind == 'jones-nontrivial-evaluation':
            return verify_jones_witness(current, witness)
        return False
    except (KeyError, TypeError, ValueError, ArithmeticError, AttributeError, IndexError):
        return False
