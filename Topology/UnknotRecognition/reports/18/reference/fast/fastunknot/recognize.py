"""Exact recognition pipeline (version 0.3).

Input is a validated classical one-component Diagram. The command-line loader
performs that validation; constructing Diagram(pd) directly is a validity promise.

Checked source braids first use exact at-most-three-strand recognition or a
Bennequin obstruction. The default then attempts a linear signed Seifert-graph
certificate. When
inconclusive, it follows the established pipeline: Reidemeister I/II reduction,
descending test, visible connected-sum factorization, modular Alexander/Jones
obstructions, optional exact Alexander, late Reidemeister III, and F2 Khovanov.

The standard Khovanov scanner remains the default. Optional shared, saturated,
and euler backends compress literal direct summands; saturated modes preserve
only a capped rank or a certified lower bound, as named in their evidence.
Filters never interpret agreement with the unknot invariant as triviality.
An optional twist backend uses checked source-braid runs after the filters.
If visible factors remain undecided it computes the entire original source,
never treating that braid as a presentation of one factor.
Object/time exhaustion in the backend yields UNKNOWN. An exhausted optional
Euler inference budget falls back to complete saturated scanning.

The implementation retains an exponential worst-case upper bound. The new
parameterized theorem is not a general quasi-polynomial guarantee.
"""
from __future__ import annotations

from time import monotonic
TYPE_CHECKING = False            # annotations only: importing typing costs 4.6 ms at start-up
if TYPE_CHECKING:
    from typing import Any

from .alexander import alexander_polynomial, evaluate, format_polynomial
from .braid import braid_certificate
from .diagram import Diagram
from .factor import convolve, visible_factors
from .filters import FilterLimit, alexander_obstruction, jones_obstruction
from .interlace import visible_factors_interlacement
from .ordering import best_scan_order
from .scan import ScanLimit, khovanov_rank
from .seifert import seifert_certificate
from .simplify import descending_start, simplify


class Result:
    """The outcome of ``recognize``: a mutable record with value equality."""

    def __init__(self, status: str, method: str, input_crossings: int, reduced_crossings: int, seconds: float,
                 evidence: dict[str, Any] | None = None):
        self.status = status                  # UNKNOT, KNOTTED, UNKNOWN
        self.method = method
        self.input_crossings = input_crossings
        self.reduced_crossings = reduced_crossings
        self.seconds = seconds
        self.evidence = {} if evidence is None else evidence

    def _fields(self):
        return (self.status, self.method, self.input_crossings, self.reduced_crossings, self.seconds, self.evidence)

    def __eq__(self, other):
        return self._fields() == other._fields() if other.__class__ is self.__class__ else NotImplemented

    __hash__ = None

    def __repr__(self):
        return (f"Result(status={self.status!r}, method={self.method!r}, input_crossings={self.input_crossings!r}, "
                f"reduced_crossings={self.reduced_crossings!r}, seconds={self.seconds!r}, evidence={self.evidence!r})")

    @property
    def is_unknot(self) -> bool | None:
        return {"UNKNOT": True, "KNOTTED": False}.get(self.status)

    def to_json(self) -> dict[str, Any]:
        return {
            "status": self.status, "is_unknot": self.is_unknot, "method": self.method,
            "input_crossings": self.input_crossings, "reduced_crossings": self.reduced_crossings,
            "seconds": round(self.seconds, 6), "evidence": self.evidence,
            "quasipolynomial_guarantee": False,
            "worst_case": "2^O(n) upper bound; no general quasi-polynomial guarantee for the Khovanov backends",
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


def _decide_twist(source: Diagram, evidence: dict, *, max_basis, deadline, check_d_squared):
    """Decide the entire checked source knot, never an unmatched PD factor."""
    from .twist.core import Budget
    from .twist_adapter import twist_khovanov_rank
    remaining = None if deadline is None else max(0.0, deadline - monotonic())
    kh = twist_khovanov_rank(source, check_d_squared=check_d_squared,
                            budget=Budget(max_basis=max_basis, seconds=remaining))
    evidence["khovanov"] = {
        "field": "F2", "backend": "twist", "unreduced_rank": kh["rank"],
        "reduced_rank": kh["reduced_rank"],
        "unreduced_rank_by_cube_degree": kh["by_degree"],
        "grading_diagram": kh["grading_diagram"], "source_crossings": kh["source_crossings"],
        "source_strands": kh["source_strands"], "macro_reduced_by_degree": kh["macro_reduced_by_degree"],
        "preflight": kh["preflight"], "scan_stats": kh["stats"],
    }
    return ("UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED"), "twist-khovanov-F2"


def _decide_prime_looking(diagram: Diagram, evidence: dict, *, use_modular, use_jones, use_alexander,
                          use_exact_alexander, use_r3, use_descending,
                          jones_max_states, jones_max_transitions, max_objects, deadline,
                          check_d_squared, scan_options, twist_source=None, defer_twist=False) -> tuple[str, str]:
    """Verdict and method for one summand (already simplified by the caller)."""
    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted")

    if use_modular:
        witness = alexander_obstruction(diagram, check=check)
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
    backend = scan_options["backend"]
    if backend == "twist":
        if twist_source is None:
            if defer_twist:
                evidence["twist_deferred"] = "source braid represents the whole connected sum"
                return "INCONCLUSIVE", "twist-deferred"
            evidence["twist_skipped"] = "no checked source braid for this diagram or factor"
            backend = "standard"
        else:
            return _decide_twist(twist_source, evidence, max_basis=scan_options["twist_max_basis"],
                                 deadline=deadline, check_d_squared=check_d_squared)
    if backend == "euler":
        from .euler_scan import euler_compressed_khovanov_decide
        kh = euler_compressed_khovanov_decide(
            diagram.pd, order=order, max_objects=max_objects, seconds=remaining,
            check_d_squared=check_d_squared, euler_max_states=scan_options["euler_max_states"])
        evidence["khovanov"] = {"field": "F2", **kh}
        method = "component-euler-bound" if kh["method"] == "component-euler" else "khovanov-component-sharing-saturated"
        return kh["status"], method
    if backend == "saturated":
        from .component_scan import compressed_khovanov_decide
        kh = compressed_khovanov_decide(diagram.pd, order=order, max_objects=max_objects,
                                       seconds=remaining, check_d_squared=check_d_squared)
        evidence["khovanov"] = {"field": "F2", "rank_capped": kh["rank_capped"],
                                "rank_cap": 3, "scan_stats": kh["stats"],
                                "scan_order": kh["order"], "backend": kh["backend"]}
        return kh["status"], "khovanov-component-sharing-saturated"
    if backend == "shared":
        from .component_scan import compressed_khovanov_rank
        kh = compressed_khovanov_rank(diagram.pd, order=order, max_objects=max_objects,
                                     seconds=remaining, check_d_squared=check_d_squared)
    else:
        standard_options = {key: value for key, value in scan_options.items()
                            if key not in ("backend", "euler_max_states", "twist_max_basis")}
        kh = khovanov_rank(diagram.pd, order=order, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared, **standard_options)
    evidence["khovanov"] = {"field": "F2", "unreduced_rank": kh["rank"], "reduced_rank": kh["reduced_rank"],
                            "unreduced_rank_by_cube_degree": kh["by_degree"], "scan_stats": kh["stats"],
                            "scan_order": kh["order"]}
    if "composition" in kh:
        evidence["khovanov"]["composition"] = kh["composition"]
        evidence["khovanov"]["composition_stats"] = kh["composition_stats"]
    if "race_winner" in kh:
        evidence["khovanov"]["race_winner"] = kh["race_winner"]
    method = "reduced-khovanov-F2-shared" if backend == "shared" else "reduced-khovanov-F2-scan"
    return ("UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED"), method


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_seifert: bool = True, backend: str = "standard",
              use_braid: bool = True, braid_backend: str = "free-product",
              use_braid_reduction: bool = True,
              euler_max_states: int | None = 4096,
              use_factorization: bool = True, use_modular: bool = True, use_jones: bool = True,
              use_alexander: bool = True, use_exact_alexander: bool | None = None, use_r3: bool = True,
              jones_max_states: int | None = 4096,
              jones_max_transitions: int | None = 200_000, max_objects: int | None = None,
              seconds: float | None = None, check_d_squared: bool = False,
              pivot: str = "minfill", algebra: str = "bits", tail: int = 0,
              race: int = 1, race_after: float = 1.0,
              factor_backend: str = "interlacement", composition: str = "standard",
              composition_max_variables: int = 18, twist_max_basis: int = 1_000_000) -> Result:
    start = monotonic()
    if type(twist_max_basis) is not int or twist_max_basis < 0:
        raise ValueError("twist_max_basis must be nonnegative")
    if composition not in ("standard", "component", "component-dense"):
        raise ValueError("composition must be standard, component, or component-dense")
    if type(composition_max_variables) is not int or composition_max_variables < 0:
        raise ValueError("composition_max_variables must be nonnegative")
    if composition != "standard" and (backend != "standard" or pivot != "minfill" or algebra != "bits" or race != 1):
        raise ValueError("component composition requires standard backend, minfill, bits, and race=1")
    if braid_backend not in ("free-product", "matrix"):
        raise ValueError("braid_backend must be free-product or matrix")
    if factor_backend not in ("interlacement", "legacy"):
        raise ValueError("factor_backend must be interlacement or legacy")
    if backend not in ("standard", "shared", "saturated", "euler", "twist"):
        raise ValueError("backend must be standard, shared, saturated, euler, or twist")
    if euler_max_states is not None and (type(euler_max_states) is not int or euler_max_states < 0):
        raise ValueError("euler_max_states must be a nonnegative integer or None")
    if backend != "standard" and (pivot != "minfill" or algebra != "bits" or tail != 0 or race != 1):
        raise ValueError("alternate backends require minfill pivots, bits algebra, tail=0, and race=1")
    deadline = None if seconds is None else start + seconds
    original = diagram
    evidence: dict[str, Any] = {}
    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted")

    try:
        check()
        if use_braid and original.braid_source is not None:
            strands, word = original.braid_source
            witness = braid_certificate(strands, word, backend=braid_backend,
                                        use_braid_reduction=False, check=check)
            check()
            evidence["braid"] = witness
            if witness["status"] != "INCONCLUSIVE":
                return Result(witness["status"], witness["method"], original.crossings,
                              diagram.crossings, monotonic() - start, evidence)
        if use_seifert:
            certificate = seifert_certificate(diagram)
            check()
            if certificate is not None:
                evidence["seifert_certificate"] = certificate
                return Result(certificate["status"], certificate["criterion"], diagram.crossings,
                              diagram.crossings, monotonic() - start, evidence)
        if use_reduction:
            diagram, trace = simplify(diagram, r3=False)      # Reidemeister III waits until the filters have failed
            check()
            evidence["reidemeister_trace"] = [m.to_json() for m in trace]
        if diagram.crossings == 0:
            return Result("UNKNOT", "reidemeister-reduction", original.crossings, 0, monotonic() - start, evidence)
        if use_seifert and diagram.crossings < original.crossings:
            # Cancelling opposite-sign crossings can expose homogeneity even when
            # the original signed graph was inconclusive. Replay the reduction
            # trace before checking this certificate: it describes the new diagram.
            certificate = seifert_certificate(diagram)
            check()
            if certificate is not None:
                evidence["seifert_after_reduction"] = certificate
                return Result(certificate["status"], "reduced-" + certificate["criterion"],
                              original.crossings, diagram.crossings, monotonic() - start, evidence)
        if use_descending:
            dart = descending_start(diagram)
            check()
            if dart is not None:
                evidence["descending_start_dart"] = dart
                return Result("UNKNOT", "descending-diagram", original.crossings, diagram.crossings,
                              monotonic() - start, evidence)
        # Endpoint descent may cost O(n*m), so the cheaper structural and
        # diagram certificates get priority. The retained original source has
        # the same closure as the diagram after its recorded reductions.
        if (use_braid and use_braid_reduction and original.braid_source is not None
                and original.braid_source[0] > 3):
            strands, word = original.braid_source
            witness = braid_certificate(strands, word, backend=braid_backend,
                                        use_braid_reduction=True, check=check)
            check()
            evidence["braid"] = witness
            if witness["status"] != "INCONCLUSIVE":
                return Result(witness["status"], witness["method"], original.crossings,
                              diagram.crossings, monotonic() - start, evidence)
        factors = [diagram]
        if use_factorization:
            check()
            if factor_backend == "interlacement":
                factors, certificate = visible_factors_interlacement(diagram, check=check)
                if len(factors) > 1:
                    evidence["connected_sum_factorization"] = certificate
            else:
                factors, cuts = visible_factors(diagram, check=check)
                if cuts:
                    evidence["connected_sum_cuts"] = cuts
            check()
        options = dict(use_modular=use_modular and use_alexander, use_jones=use_jones, use_alexander=use_alexander,
                       use_exact_alexander=use_exact_alexander, use_r3=use_r3 and use_reduction,
                       use_descending=use_descending,
                       jones_max_states=jones_max_states, jones_max_transitions=jones_max_transitions,
                       max_objects=max_objects, deadline=deadline, check_d_squared=check_d_squared,
                       scan_options=dict(pivot=pivot, algebra=algebra, tail=tail, race=race,
                                         race_after=race_after, backend=backend,
                                         euler_max_states=euler_max_states, composition=composition,
                                         composition_max_variables=composition_max_variables,
                                         twist_max_basis=twist_max_basis))
        method = "reduced-khovanov-F2-scan"
        check()
        if len(factors) == 1:
            # A retained source represents this whole knot across recorded
            # reductions. Never pass it to the individual factors below.
            source = original if original.braid_source is not None else None
            status, method = _decide_prime_looking(diagram, evidence, twist_source=source, **options)
        else:
            status, reports = "UNKNOT", []
            deferred = False
            evidence["factors"] = reports
            for factor in sorted(factors, key=lambda d: d.crossings):
                check()
                sub: dict[str, Any] = {"crossings": factor.crossings}
                reports.append(sub)
                reduced, trace = simplify(factor, r3=False) if use_reduction else (factor, [])
                if reduced.crossings == 0 or (use_descending and descending_start(reduced) is not None):
                    sub["status"], sub["method"] = "UNKNOT", "reduction-or-descending"
                    continue
                sub["status"], sub["method"] = _decide_prime_looking(
                    reduced, sub, defer_twist=backend == "twist" and original.braid_source is not None, **options)
                deferred |= sub["status"] == "INCONCLUSIVE"
                check()
                if sub["status"] == "KNOTTED":
                    status, method = "KNOTTED", "connected-sum-factor:" + sub["method"]
                    break
            else:
                if deferred:
                    status, method = _decide_twist(original, evidence, max_basis=twist_max_basis,
                                                  deadline=deadline, check_d_squared=check_d_squared)
                else:
                    method = "connected-sum-all-factors-trivial"
        check()
    except (ScanLimit, MemoryError) as exc:
        evidence["reason"] = str(exc) or "memory allocation failed"
        return Result("UNKNOWN", "resource-limit", original.crossings, diagram.crossings,
                      monotonic() - start, evidence)
    return Result(status, method, original.crossings, diagram.crossings, monotonic() - start, evidence)

