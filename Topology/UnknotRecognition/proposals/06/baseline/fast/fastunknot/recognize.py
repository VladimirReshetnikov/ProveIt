"""The recognition pipeline.

1. validate the diagram (one component, spherical rotation system);
2. crossing-decreasing Reidemeister I/II moves (polynomial);
3. descending-diagram test (polynomial, sufficient for UNKNOT);
4. Alexander polynomial (polynomial; a value other than 1 certifies KNOTTED);
5. reduced Khovanov rank over F2 by scanning (exact; UNKNOT iff rank 1).

Every verdict is exact.  Optional ceilings turn a too-expensive step 5 into
UNKNOWN, never into a knot verdict.  Worst-case running time is exponential
in the crossing number; it is not quasi-polynomial.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from time import monotonic
from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .scan import ScanLimit, khovanov_rank
from .simplify import descending_start, simplify


@dataclass
class Result:
    status: str                  # UNKNOT, KNOTTED, UNKNOWN
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
            "worst_case": "2^O(n); the scan is exponential in its boundary size, not in n",
        }


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_alexander: bool = True, max_objects: int | None = None,
              seconds: float | None = None, check_d_squared: bool = False) -> Result:
    start = monotonic()
    original = diagram
    evidence: dict[str, Any] = {}
    trace = []
    if use_reduction:
        diagram, trace = simplify(diagram)
        evidence["reidemeister_trace"] = [m.to_json() for m in trace]
    if diagram.crossings == 0:
        return Result("UNKNOT", "reidemeister-reduction", original.crossings, 0,
                      monotonic() - start, evidence)
    if use_descending:
        dart = descending_start(diagram)
        if dart is not None:
            evidence["descending_start_dart"] = dart
            return Result("UNKNOT", "descending-diagram", original.crossings, diagram.crossings,
                          monotonic() - start, evidence)
    if use_alexander:
        poly = alexander_polynomial(diagram)
        evidence["alexander_polynomial"] = format_polynomial(poly)
        evidence["determinant"] = abs(evaluate(poly, -1))
        if poly != [1]:
            return Result("KNOTTED", "alexander-polynomial", original.crossings,
                          diagram.crossings, monotonic() - start, evidence)
    remaining = None if seconds is None else max(0.0, seconds - (monotonic() - start))
    try:
        kh = khovanov_rank(diagram.pd, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared)
    except (ScanLimit, MemoryError) as exc:
        evidence["reason"] = str(exc) or "memory allocation failed"
        return Result("UNKNOWN", "resource-limit", original.crossings, diagram.crossings,
                      monotonic() - start, evidence)
    evidence["khovanov"] = {"field": "F2", "unreduced_rank": kh["rank"],
                            "reduced_rank": kh["reduced_rank"],
                            "unreduced_rank_by_cube_degree": kh["by_degree"],
                            "scan_stats": kh["stats"], "scan_order": kh["order"]}
    status = "UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED"
    return Result(status, "reduced-khovanov-F2-scan", original.crossings, diagram.crossings,
                  monotonic() - start, evidence)
