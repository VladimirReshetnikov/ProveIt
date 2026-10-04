"""Complete exact recognizer, with bounded one-sided filters before Khovanov.

A failed filter is inconclusive; a resource limit is UNKNOWN. The exponential
fallback and the mathematical meaning of both exact verdicts are unchanged.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from hashlib import sha256
import json
from math import isfinite
from time import monotonic
from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .filters import FilterLimit, determinant_residue, jones_evaluation
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
            "worst_case": "2^O(n); no width-only bound is asserted for Khovanov multiplicities",
        }


def diagram_digest(diagram: Diagram) -> str:
    data = json.dumps(diagram.to_json(), separators=(",", ":"), sort_keys=True).encode()
    return sha256(data).hexdigest()


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_alexander: bool = True, use_filters: bool = True,
              max_objects: int | None = None, seconds: float | None = None,
              check_d_squared: bool = False, jones_max_states: int = 50_000,
              jones_max_transitions: int = 1_000_000) -> Result:
    """Recognize a validated knot diagram.

    use_filters=False selects the old pipeline, but still uses the accelerated
    simplifier, order builder, and Khovanov engine. max_objects applies only to
    Khovanov: a cheaper filter may decide a knot without entering that engine.
    A Jones work cap skips that filter; a global time limit stops the pipeline.
    """
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative or None")
    for name, cap in (("max_objects", max_objects), ("jones_max_states", jones_max_states),
                      ("jones_max_transitions", jones_max_transitions)):
        if cap is not None and (type(cap) is not int or cap < 1):
            raise ValueError(f"{name} must be a positive integer or None")
    start = monotonic()
    deadline = None if seconds is None else start + seconds
    original = diagram
    evidence: dict[str, Any] = {"input_sha256": diagram_digest(diagram)}

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")

    def result(status, method):
        return Result(status, method, original.crossings, diagram.crossings,
                      monotonic() - start, evidence)

    try:
        check()
        if use_reduction:
            diagram, trace = simplify(diagram, deadline=deadline)
            evidence["reidemeister_trace"] = [m.to_json() for m in trace]
        if diagram.crossings == 0:
            return result("UNKNOT", "reidemeister-reduction")
        if use_descending:
            dart = descending_start(diagram)
            if dart is not None:
                evidence["descending_start_dart"] = dart
                return result("UNKNOT", "descending-diagram")
        check()
        if use_filters:
            det = determinant_residue(diagram, deadline=deadline)
            evidence["modular_determinant"] = det
            if det["obstructs"]:
                return result("KNOTTED", "modular-determinant")
            try:
                jones = jones_evaluation(diagram, max_states=jones_max_states,
                                         max_transitions=jones_max_transitions,
                                         deadline=deadline)
                evidence["jones_evaluation"] = jones
                if jones["obstructs"]:
                    return result("KNOTTED", "modular-jones")
            except FilterLimit as exc:
                evidence["jones_skipped"] = str(exc)
        check()
        if use_alexander:
            poly = alexander_polynomial(diagram)
            evidence["alexander_polynomial"] = format_polynomial(poly)
            evidence["determinant"] = abs(evaluate(poly, -1))
            if poly != [1]:
                return result("KNOTTED", "alexander-polynomial")
        check()
        remaining = None if deadline is None else max(0.0, deadline - monotonic())
        kh = khovanov_rank(diagram.pd, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared)
        evidence["khovanov"] = {
            "field": "F2", "unreduced_rank": kh["rank"], "reduced_rank": kh["reduced_rank"],
            "unreduced_rank_by_cube_degree": kh["by_degree"],
            "scan_stats": kh["stats"], "scan_order": kh["order"],
        }
        status = "UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED"
        return result(status, "reduced-khovanov-F2-scan")
    except (ScanLimit, MemoryError) as exc:
        evidence["reason"] = str(exc) or "memory allocation failed"
        return result("UNKNOWN", "resource-limit")
