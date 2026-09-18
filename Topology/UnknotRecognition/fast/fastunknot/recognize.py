"""The recognition pipeline (version 0.2).

1. validate the diagram (one component, spherical rotation system);
2. crossing-decreasing Reidemeister I/II moves (polynomial);
3. descending-diagram test (linear; sufficient for UNKNOT);
4. split along visible two-edge cuts; a connected sum is trivial exactly when
   every summand is, so the summands are examined separately, smallest first,
   and the first knotted summand decides;
   for each summand:
5. Alexander minor in a prime field at t = -1 and t = 2 (cubic; KNOTTED or
   inconclusive);
6. Kauffman bracket at A = 2 in a prime field by a width-bounded scan
   (KNOTTED, inconclusive, or skipped when its budget is exhausted);
7. exact Alexander polynomial over Z[t] (KNOTTED or inconclusive);
8. reduced Khovanov rank over F2 by scanning (exact; UNKNOT iff rank 1).

Every verdict is exact.  Filters 5-7 can only say KNOTTED; agreement with the
unknot's value is never evidence of triviality.  Optional ceilings turn a
too-expensive step 8 into UNKNOWN, never into a knot verdict.  Worst-case
running time is exponential in the crossing number; it is not quasi-polynomial.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from time import monotonic
from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .diagram import Diagram
from .factor import convolve, visible_factors
from .filters import FilterLimit, alexander_obstruction, jones_obstruction
from .ordering import best_scan_order
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
            "worst_case": "2^O(n); filters are polynomial or width-bounded, the Khovanov scan is not",
        }


def factored_khovanov_rank(diagram: Diagram, **options) -> dict[str, Any]:
    """F2 Khovanov ranks of a diagram as a product over its visible summands.

    Reduced ranks multiply and reduced degree counts convolve; the unreduced
    counts are twice the reduced ones.  The result can be astronomically larger
    than anything an explicit complex could hold.
    """
    seconds = options.pop("seconds", None)
    deadline = None if seconds is None else monotonic() + seconds
    factors, cuts = visible_factors(diagram)
    reduced = {0: 1}
    memo: dict = {}
    summaries = []
    stats: dict[str, int] = {}
    for factor in factors:
        if factor.pd not in memo:
            left = None if deadline is None else max(0.0, deadline - monotonic())
            memo[factor.pd] = khovanov_rank(factor.pd, seconds=left, **options)
            for key, value in memo[factor.pd]["stats"].items():
                stats[key] = max(stats.get(key, 0), value) if key.startswith("max_") else stats.get(key, 0) + value
        result = memo[factor.pd]
        if any(v % 2 for v in result["by_degree"].values()):
            raise ArithmeticError("unreduced F2 ranks of a knot must be even in every degree")
        reduced = convolve(reduced, {h: v // 2 for h, v in result["by_degree"].items()})
        summaries.append({"crossings": factor.crossings, "reduced_rank": result["reduced_rank"]})
    total = sum(reduced.values())
    return {"rank": 2 * total, "reduced_rank": total, "by_degree": {h: 2 * v for h, v in reduced.items()},
            "stats": stats, "factors": summaries, "cuts": cuts, "distinct_factors": len(memo)}


def _decide_prime_looking(diagram: Diagram, evidence: dict, *, use_modular, use_jones, use_alexander,
                          use_exact_alexander, use_r3, use_descending,
                          jones_max_states, jones_max_transitions, max_objects, deadline,
                          check_d_squared, scan_options) -> tuple[str, str]:
    """Verdict and method for one summand (already simplified by the caller)."""
    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted")

    if use_modular:
        witness = alexander_obstruction(diagram)
        if witness is not None:
            evidence["alexander_modular"] = witness
            return "KNOTTED", "alexander-modular"
    order = None
    if use_jones:
        # the Jones scan and the Khovanov scan use the same greedy order: compute it once
        order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12), check=check)
        try:
            witness = jones_obstruction(diagram, max_states=jones_max_states,
                                        max_transitions=jones_max_transitions, order=order, check=check)
        except FilterLimit as exc:
            evidence["jones"] = f"skipped: {exc}"
        else:
            if witness is not None:
                evidence["jones"] = witness
                return "KNOTTED", "jones-modular"
            evidence["jones"] = "inconclusive"
    # The exact polynomial over Z[t] can only say KNOTTED, and only if the polynomial is not a
    # unit, which the modular test has just failed to see at t = -1 and at a generic point of
    # F_p.  On filter-undecided unknot diagrams of 15 to 27 crossings it took a median 24% (up
    # to 63%) of the whole recognition, so by default it runs only when the modular test did not.
    exact = use_alexander and (not use_modular if use_exact_alexander is None else use_exact_alexander)
    if use_alexander and not exact:
        evidence["alexander_polynomial"] = ("not computed: the first minor is a unit at t = -1 and at a "
                                            "generic point of F_p (use_exact_alexander=True computes it)")
    if exact:
        check()
        poly = alexander_polynomial(diagram)
        evidence["alexander_polynomial"] = format_polynomial(poly)
        evidence["determinant"] = abs(evaluate(poly, -1))
        if poly != [1]:
            return "KNOTTED", "alexander-polynomial"
    if use_r3:
        # Every filter has failed, so the exponential scan is next: now it pays to look for
        # Reidemeister III moves that unlock further I/II reductions.  (Done earlier, the search
        # cost up to 58% on diagrams that the Alexander test decides a moment later.)
        check()
        reduced, trace = simplify(diagram, r3=True)
        if reduced.crossings < diagram.crossings:
            evidence["reidemeister_three"] = {"crossings_before": diagram.crossings,
                                              "crossings_after": reduced.crossings,
                                              "trace": [m.to_json() for m in trace]}
            if reduced.crossings == 0:
                return "UNKNOT", "reidemeister-reduction"
            if use_descending and descending_start(reduced) is not None:
                return "UNKNOT", "descending-diagram"
            diagram, order = reduced, None
    remaining = None if deadline is None else max(0.0, deadline - monotonic())
    kh = khovanov_rank(diagram.pd, order=order, max_objects=max_objects, seconds=remaining,
                       check_d_squared=check_d_squared, **scan_options)
    evidence["khovanov"] = {"field": "F2", "unreduced_rank": kh["rank"], "reduced_rank": kh["reduced_rank"],
                            "unreduced_rank_by_cube_degree": kh["by_degree"], "scan_stats": kh["stats"],
                            "scan_order": kh["order"]}
    return ("UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED"), "reduced-khovanov-F2-scan"


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_factorization: bool = True, use_modular: bool = True, use_jones: bool = True,
              use_alexander: bool = True, use_exact_alexander: bool | None = None, use_r3: bool = True,
              jones_max_states: int | None = 4096,
              jones_max_transitions: int | None = 200_000, max_objects: int | None = None,
              seconds: float | None = None, check_d_squared: bool = False,
              pivot: str = "minfill", algebra: str = "bits", tail: int = 0) -> Result:
    start = monotonic()
    deadline = None if seconds is None else start + seconds
    original = diagram
    evidence: dict[str, Any] = {}
    if use_reduction:
        diagram, trace = simplify(diagram, r3=False)      # Reidemeister III waits until the filters have failed
        evidence["reidemeister_trace"] = [m.to_json() for m in trace]
    if diagram.crossings == 0:
        return Result("UNKNOT", "reidemeister-reduction", original.crossings, 0, monotonic() - start, evidence)
    if use_descending:
        dart = descending_start(diagram)
        if dart is not None:
            evidence["descending_start_dart"] = dart
            return Result("UNKNOT", "descending-diagram", original.crossings, diagram.crossings,
                          monotonic() - start, evidence)
    factors = [diagram]
    if use_factorization:
        factors, cuts = visible_factors(diagram)
        if cuts:
            evidence["connected_sum_cuts"] = cuts
    options = dict(use_modular=use_modular and use_alexander, use_jones=use_jones, use_alexander=use_alexander,
                   use_exact_alexander=use_exact_alexander, use_r3=use_r3 and use_reduction,
                   use_descending=use_descending,
                   jones_max_states=jones_max_states, jones_max_transitions=jones_max_transitions,
                   max_objects=max_objects, deadline=deadline, check_d_squared=check_d_squared,
                   scan_options=dict(pivot=pivot, algebra=algebra, tail=tail))
    method = "reduced-khovanov-F2-scan"
    try:
        if len(factors) == 1:
            status, method = _decide_prime_looking(diagram, evidence, **options)
        else:
            status, reports = "UNKNOT", []
            evidence["factors"] = reports
            for factor in sorted(factors, key=lambda d: d.crossings):
                sub: dict[str, Any] = {"crossings": factor.crossings}
                reports.append(sub)
                reduced, trace = simplify(factor, r3=False) if use_reduction else (factor, [])
                if reduced.crossings == 0 or (use_descending and descending_start(reduced) is not None):
                    sub["status"], sub["method"] = "UNKNOT", "reduction-or-descending"
                    continue
                sub["status"], sub["method"] = _decide_prime_looking(reduced, sub, **options)
                if sub["status"] == "KNOTTED":
                    status, method = "KNOTTED", "connected-sum-factor:" + sub["method"]
                    break
            else:
                method = "connected-sum-all-factors-trivial"
    except (ScanLimit, MemoryError) as exc:
        evidence["reason"] = str(exc) or "memory allocation failed"
        return Result("UNKNOWN", "resource-limit", original.crossings, diagram.crossings,
                      monotonic() - start, evidence)
    return Result(status, method, original.crossings, diagram.crossings, monotonic() - start, evidence)
