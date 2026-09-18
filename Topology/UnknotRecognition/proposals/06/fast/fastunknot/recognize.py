"""Exact unknot recognition with one-sided filters and an exact fallback.

Polynomial Reidemeister/descending/Alexander preprocessing is followed by a
bounded, deterministic modular Jones obstruction. An inconclusive obstruction
falls through to the optimized Khovanov scan, optionally using visible sums.
No general quasi-polynomial bound is claimed.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from math import isfinite
from time import monotonic
from typing import Any
from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .jones import normalized_bracket_mod
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
        return {"status": self.status, "is_unknot": self.is_unknot, "method": self.method,
                "input_crossings": self.input_crossings,
                "reduced_crossings": self.reduced_crossings,
                "seconds": round(self.seconds, 6), "evidence": self.evidence,
                "quasipolynomial_guarantee": False,
                "worst_case": "2^O(n); no general boundary-width-only bound is asserted"}


def recognize(diagram: Diagram, *, use_reduction: bool = True,
              use_descending: bool = True, use_alexander: bool = True,
              use_jones: bool = True, jones_max_states: int = 4096,
              decompose: bool = True, tail_crossings: int = 2,
              max_objects: int | None = None, seconds: float | None = None,
              check_d_squared: bool = False) -> Result:
    """Decide a knot, or return UNKNOWN when a requested resource ceiling hits.

    Jones equality is *never* an UNKNOT result. A Jones state overflow merely
    skips that filter. ``seconds`` is a cooperative, not OS-enforced, deadline.
    """
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError("max_objects must be a positive integer or None")
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    if type(jones_max_states) is not int or jones_max_states < 1:
        raise ValueError("jones_max_states must be a positive integer")
    if type(tail_crossings) is not int or tail_crossings < 1:
        raise ValueError("tail_crossings must be a positive integer")
    start = monotonic()
    original = diagram
    deadline = None if seconds is None else start + seconds
    evidence: dict[str, Any] = {}
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
        check()
        if use_descending:
            dart = descending_start(diagram, deadline=deadline)
            if dart is not None:
                evidence["descending_start_dart"] = dart
                return result("UNKNOT", "descending-diagram")
        check()
        if use_alexander:
            poly = alexander_polynomial(diagram, deadline=deadline)
            evidence["alexander_polynomial"] = format_polynomial(poly)
            evidence["determinant"] = abs(evaluate(poly, -1))
            if poly != [1]:
                return result("KNOTTED", "alexander-polynomial")
        check()
        if use_jones:
            jones = normalized_bracket_mod(diagram, max_states=jones_max_states,
                                          deadline=deadline)
            evidence["jones"] = jones
            if jones["completed"] and jones["value"] != 1:
                return result("KNOTTED", "modular-jones")
        check()
        remaining = None if deadline is None else max(0.0, deadline - monotonic())
        kh = khovanov_rank(diagram.pd, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared, decompose=decompose,
                           tail_crossings=tail_crossings)
        evidence["khovanov"] = {"field": "F2", "unreduced_rank": kh["rank"],
                                 "reduced_rank": kh["reduced_rank"],
                                 "unreduced_rank_by_cube_degree": kh["by_degree"],
                                 "scan_stats": kh["stats"], "scan_order": kh["order"]}
        if "decomposition" in kh:
            evidence["khovanov"]["decomposition"] = kh["decomposition"]
            evidence["khovanov"]["factor_results"] = kh["factor_results"]
        return result("UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED",
                      "reduced-khovanov-F2-scan")
    except (ScanLimit, MemoryError) as exc:
        evidence["reason"] = str(exc) or "memory allocation failed"
        return result("UNKNOWN", "resource-limit")
