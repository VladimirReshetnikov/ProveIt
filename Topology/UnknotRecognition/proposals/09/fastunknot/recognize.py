"""Exact recognition with bounded one-sided filters and a complete fallback.

New default order: R1/R2 -> descending -> modular determinant -> modular Jones
-> full Alexander -> factor-aware Khovanov over F2. A filter matching the
unknot is INCONCLUSIVE. Only a proven topological simplification or the exact
homology criterion produces UNKNOT. Resource exhaustion produces UNKNOWN.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from math import isfinite
from time import monotonic
from typing import Any
from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .scan import ScanLimit, khovanov_rank
from .simplify import descending_start, simplify
from .determinant_filter import determinant_residue
from .jones import JonesLimit, jones_residue


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
                "input_crossings": self.input_crossings, "reduced_crossings": self.reduced_crossings,
                "seconds": round(self.seconds, 6), "evidence": self.evidence,
                "quasipolynomial_guarantee": False,
                "worst_case": "2^O(n); no width-only bound for full Khovanov multiplicities"}


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_alexander: bool = True, use_determinant: bool = True, use_jones: bool = True,
              use_factors: bool = True, max_jones_states: int | None = 8192,
              max_jones_transitions: int | None = 250000, max_objects: int | None = None,
              seconds: float | None = None, check_d_squared: bool = False) -> Result:
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    for name, value in (("max_objects", max_objects), ("max_jones_states", max_jones_states),
                        ("max_jones_transitions", max_jones_transitions)):
        if value is not None and (type(value) is not int or value < 1):
            raise ValueError(f"{name} must be a positive integer or None")
    start = monotonic()
    deadline = None if seconds is None else start + seconds
    # Frozen dataclass construction is public: revalidate even a directly constructed object.
    diagram = Diagram.from_pd(diagram.pd)
    original_n = diagram.crossings
    evidence: dict[str, Any] = {}

    def result(status, method):
        return Result(status, method, original_n, diagram.crossings, monotonic() - start, evidence)

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")

    try:
        if diagram.crossings:
            check()
        if use_reduction:
            diagram, trace = simplify(diagram, deadline=deadline)
            evidence["reidemeister_trace"] = [m.to_json() for m in trace]
        if not diagram.crossings:
            return result("UNKNOT", "reidemeister-reduction")
        check()
        if use_descending:
            dart = descending_start(diagram)
            if dart is not None:
                evidence["descending_start_dart"] = dart
                return result("UNKNOT", "descending-diagram")
        check()
        if use_alexander and use_determinant:
            obstruction = determinant_residue(diagram, deadline=deadline)
            evidence["determinant_modular"] = obstruction
            if obstruction["obstructs"]:
                return result("KNOTTED", "modular-determinant")
        if use_jones:
            check()
            try:
                obstruction = jones_residue(diagram, max_states=max_jones_states,
                                            max_transitions=max_jones_transitions, deadline=deadline)
                evidence["jones_modular"] = obstruction
                if obstruction["obstructs"]:
                    return result("KNOTTED", "modular-jones")
            except JonesLimit as exc:
                evidence["jones_filter_inconclusive"] = str(exc)
                check()  # A FILTER cap allows fallback; a GLOBAL time cap does not.
        if use_alexander:
            check()
            poly = alexander_polynomial(diagram, deadline=deadline)
            evidence["alexander_polynomial"] = format_polynomial(poly)
            evidence["determinant"] = abs(evaluate(poly, -1))
            if poly != [1]:
                return result("KNOTTED", "alexander-polynomial")
        check()
        remaining = None if deadline is None else max(0.0, deadline - monotonic())
        kh = khovanov_rank(diagram.pd, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared, factor=use_factors)
        evidence["khovanov"] = {"field": "F2", "unreduced_rank": kh["rank"],
                                "reduced_rank": kh["reduced_rank"],
                                "unreduced_rank_by_cube_degree": kh["by_degree"],
                                "scan_stats": kh["stats"], "scan_order": kh["order"]}
        if "factors" in kh:
            evidence["khovanov"].update({"factors": kh["factors"],
                                        "factor_certificate": kh["factor_certificate"]})
        return result("UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED",
                      "reduced-khovanov-F2-scan")
    except (ScanLimit, MemoryError) as exc:
        evidence["reason"] = str(exc) or "memory allocation failed"
        return result("UNKNOWN", "resource-limit")
