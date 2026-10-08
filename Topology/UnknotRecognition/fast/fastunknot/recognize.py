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
from .filters import FilterLimit, alexander_obstruction
from .jones_filter import select_jones_filter, validate_jones_options
from .interlace import visible_factors_interlacement
from .ordering import best_scan_order
from .scan import ScanLimit, khovanov_rank
from .seifert import seifert_certificate
from .simplify import descending_start, simplify, validate_r3_options


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


def _invariant_obstruction(diagram, evidence, *, use_modular, use_jones, use_alexander,
                           use_exact_alexander, jones_backend, potts_colors,
                           jones_max_states, jones_max_transitions, check):
    """One-sided polynomial filters and the scan order reusable by exact work."""
    if use_modular:
        witness = alexander_obstruction(diagram, check=check)
        if witness is not None:
            evidence["alexander_modular"] = witness
            return "alexander-modular", None
    order = None
    if use_jones:
        # the Jones scan and the Khovanov scan use the same greedy order: compute it once
        order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12), check=check)
        order_stats, witness = {}, None
        try:
            test, method, extra = select_jones_filter(jones_backend, potts_colors)
            if jones_backend in ("potts-separator", "potts-adaptive", "potts-faithful"):
                extra["statistics"] = order_stats
            witness = test(diagram, max_states=jones_max_states,
                           max_transitions=jones_max_transitions, order=order, check=check, **extra)
        except FilterLimit as exc:
            evidence["jones"] = f"skipped: {exc}"
        else:
            evidence["jones"] = witness if witness is not None else "inconclusive"
        if "order_certificate" in order_stats:
            certificate = order_stats["order_certificate"]
            order = certificate["order"]
            evidence["separator_order"] = certificate
        if "ordering_policy" in order_stats:
            evidence["jones_ordering_policy"] = order_stats["ordering_policy"]
        if "polynomial_identity" in order_stats:
            evidence["jones_polynomial_identity"] = order_stats["polynomial_identity"]
        if witness is not None:
            return method, order
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
            return "alexander-polynomial", order
    return None, order


def _decide_prime_looking(diagram: Diagram, evidence: dict, *, use_modular, use_jones, use_alexander,
                          use_exact_alexander, use_r3, use_descending,
                          jones_backend, potts_colors, jones_max_states, jones_max_transitions,
                          max_objects, deadline,
                          check_d_squared, scan_options, window_options=None,
                          twist_source=None, defer_twist=False, checked_modular=False,
                          r3_options=None) -> tuple[str, str]:
    """Verdict and method for one summand (already simplified by the caller)."""
    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted")

    method, order = _invariant_obstruction(diagram, evidence,
        use_modular=use_modular and not checked_modular, use_jones=use_jones,
        use_alexander=use_alexander, use_exact_alexander=use_exact_alexander,
        jones_backend=jones_backend, potts_colors=potts_colors,
        jones_max_states=jones_max_states, jones_max_transitions=jones_max_transitions,
        check=check)
    if method is not None:
        return "KNOTTED", method
    if use_r3:
        # Every filter has failed, so the exponential scan is next: now it pays to look for
        # Reidemeister III moves that unlock further I/II reductions.  (Done earlier, the search
        # cost up to 58% on diagrams that the Alexander test decides a moment later.)
        check()
        search_stats = {} if r3_options and r3_options["r3_search"] != "last" else None
        reduced, trace = simplify(diagram, r3=True, check=check if deadline is not None else None,
                                  stats=search_stats, **(r3_options or {}))
        if search_stats is not None:
            evidence["r3_search"] = dict(r3_options, **search_stats)
        if reduced.crossings < diagram.crossings:
            evidence["reidemeister_three"] = {"crossings_before": diagram.crossings,
                                              "crossings_after": reduced.crossings,
                                              "trace": [m.to_json() for m in trace]}
            if reduced.crossings == 0:
                return "UNKNOT", "reidemeister-reduction"
            if use_descending and descending_start(reduced) is not None:
                return "UNKNOT", "descending-diagram"
            diagram, order = reduced, None
            if 'separator_order' in evidence:
                # Crossing indices changed. Rebuild the witness on this diagram
                # before supplying an order to a window or the complete scan.
                from .separator_order import width_bounded_scan_order
                certificate = width_bounded_scan_order(diagram.pd, check=check)
                evidence['separator_order'] = certificate
                order = certificate['order']
    if window_options is not None:
        from .window_filter import probe_windows
        ceiling = window_options["max_objects"]
        if max_objects is not None:
            ceiling = max_objects if ceiling is None else min(ceiling, max_objects)
        probe = probe_windows(diagram, maximum_radius=window_options["radius"],
                              max_objects=ceiling, seconds=window_options["seconds"],
                              deadline=deadline, order=order, check_d_squared=check_d_squared,
                              reduction=scan_options["reduction"], composition=scan_options["composition"],
                              composition_max_variables=scan_options["composition_max_variables"],
                              strategy=window_options["strategy"])
        evidence["khovanov_windows"] = probe["evidence"]
        if probe["status"] != "INCONCLUSIVE":
            method = "khovanov-window-obstruction" if probe["status"] == "KNOTTED" else "khovanov-window-complete"
            return probe["status"], method
        order = probe["order"]
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
    if backend in ("barcode", "fitting"):
        if backend == "barcode":
            from .barcode_scan import barcode_khovanov_decide as decide
        else:
            from .scalar_split import fitting_khovanov_decide as decide
        kh = decide(diagram.pd, order=order, max_objects=max_objects,
                    seconds=remaining, check_d_squared=check_d_squared)
        evidence["khovanov"] = {"field": "F2", **kh}
        return kh["status"], "khovanov-" + backend + "-saturated"
    if backend == "closure":
        from .closure_scan import closure_khovanov_decide
        kh = closure_khovanov_decide(
            diagram.pd, order=order, max_objects=max_objects, seconds=remaining,
            check_d_squared=check_d_squared, closure_max_work=scan_options["closure_max_work"])
        evidence["khovanov"] = {"field": "F2", **kh}
        return kh["status"], "classical-closure-bound" if kh["method"] == "closure-bound" else "khovanov-closure-reset"
    if backend == "shadow":
        from .shadow_scan import shadow_compressed_khovanov_decide
        kh = shadow_compressed_khovanov_decide(
            diagram.pd, order=order, max_objects=max_objects, seconds=remaining,
            check_d_squared=check_d_squared, euler_max_states=scan_options["euler_max_states"],
            shadow_max_work=scan_options["shadow_max_work"])
        evidence["khovanov"] = {"field": "F2", **kh}
        method = {"marked-residue-four": "marked-residue-four-bound",
                  "component-euler": "component-euler-bound",
                  "closed-rank": "khovanov-component-sharing-saturated"}[kh["method"]]
        return kh["status"], method
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
                            if key not in ("backend", "euler_max_states", "twist_max_basis", "shadow_max_work", "closure_max_work")}
        kh = khovanov_rank(diagram.pd, order=order, max_objects=max_objects, seconds=remaining,
                           check_d_squared=check_d_squared, **standard_options)
    evidence["khovanov"] = {"field": "F2", "unreduced_rank": kh["rank"], "reduced_rank": kh["reduced_rank"],
                            "unreduced_rank_by_cube_degree": kh["by_degree"], "scan_stats": kh["stats"],
                            "scan_order": kh["order"]}
    if "composition" in kh:
        evidence["khovanov"]["composition"] = kh["composition"]
        evidence["khovanov"]["composition_stats"] = kh["composition_stats"]
    if "reduction" in kh:
        evidence["khovanov"]["reduction"] = kh["reduction"]
    if "race_winner" in kh:
        evidence["khovanov"]["race_winner"] = kh["race_winner"]
    method = "reduced-khovanov-F2-shared" if backend == "shared" else "reduced-khovanov-F2-scan"
    return ("UNKNOT" if kh["reduced_rank"] == 1 else "KNOTTED"), method


def recognize(diagram: Diagram, *, use_reduction: bool = True, use_descending: bool = True,
              use_seifert: bool = True, backend: str = "standard",
              use_braid: bool = True, braid_backend: str = "free-product",
              use_rational: bool = True,
              use_braid_reduction: bool = True, use_braid_profile: bool = False,
              euler_max_states: int | None = 4096,
              shadow_max_work: int | None = 1_000_000,
              closure_max_work: int | None = 1_000_000,
              use_factorization: bool = True, use_modular: bool = True, use_jones: bool = True,
              use_alexander: bool = True, use_exact_alexander: bool | None = None, use_r3: bool = True,
              r3_search: str = "last", r3_depth: int = 4,
              r3_budget: int | None = 10, r3_births: int = 1,
              jones_backend: str = "matching", potts_colors: int = 6,
              jones_max_states: int | None = 4096,
              jones_max_transitions: int | None = 200_000, max_objects: int | None = None,
              seconds: float | None = None, check_d_squared: bool = False,
              pivot: str = "minfill", algebra: str = "bits", tail: int = 0,
              race: int = 1, race_after: float = 1.0,
              factor_backend: str = "interlacement", composition: str = "standard",
              composition_max_variables: int = 18, twist_max_basis: int = 1_000_000,
              reduction: str = "standard", window_radius: int | None = None,
              window_max_objects: int | None = 20000, window_seconds: float | None = 0.1,
              use_ranktwo: bool = False, ranktwo_seconds: float | None = 0.1,
              use_garside: bool = False, garside_radius: int = 1,
              garside_seconds: float | None = 0.1, garside_max_ticks: int | None = 100000,
              garside_max_targets: int | None = 100000,
              window_strategy: str = "support") -> Result:
    restart_options = locals().copy() if use_ranktwo or use_garside else None
    start = monotonic()
    validate_r3_options(r3_search, r3_depth, r3_budget, r3_births)
    validate_jones_options(jones_backend, potts_colors, jones_max_states, jones_max_transitions)
    if window_strategy not in ("support", "minimal"):
        raise ValueError("window_strategy must be support or minimal")
    if type(use_braid_profile) is not bool:
        raise ValueError("use_braid_profile must be boolean")
    if type(use_rational) is not bool:
        raise ValueError("use_rational must be boolean")
    if type(use_ranktwo) is not bool:
        raise ValueError("use_ranktwo must be boolean")
    if type(use_garside) is not bool:
        raise ValueError("use_garside must be boolean")
    if type(garside_radius) is not int or garside_radius < 1:
        raise ValueError("garside_radius must be a positive integer")
    for name, value, minimum in (("garside_max_ticks", garside_max_ticks, 0),
                                 ("garside_max_targets", garside_max_targets, 1)):
        if value is not None and (type(value) is not int or value < minimum):
            raise ValueError(f"{name} must be an integer >= {minimum}, or None")
    if garside_seconds is not None:
        from math import isfinite
        if type(garside_seconds) not in (int, float) or not isfinite(garside_seconds) or garside_seconds < 0:
            raise ValueError("garside_seconds must be finite and nonnegative, or None")
    if ranktwo_seconds is not None:
        from math import isfinite
        if type(ranktwo_seconds) not in (int, float) or not isfinite(ranktwo_seconds) or ranktwo_seconds < 0:
            raise ValueError("ranktwo_seconds must be finite and nonnegative, or None")
    if window_radius is not None and (type(window_radius) is not int or window_radius < 0):
        raise ValueError("window_radius must be a nonnegative integer or None")
    if window_max_objects is not None and (type(window_max_objects) is not int or window_max_objects < 0):
        raise ValueError("window_max_objects must be a nonnegative integer or None")
    if window_seconds is not None:
        from math import isfinite
        if type(window_seconds) not in (int, float) or not isfinite(window_seconds) or window_seconds < 0:
            raise ValueError("window_seconds must be finite and nonnegative, or None")
    if reduction not in ("standard", "residue", "adaptive", "disk-adaptive", "graded", "graded-adaptive", "corridor", "corridor-adaptive"):
        raise ValueError("reduction must be standard, residue, adaptive, disk-adaptive, graded, graded-adaptive, corridor, or corridor-adaptive")
    if reduction != "standard" and (backend != "standard" or pivot != "minfill" or algebra != "bits" or race != 1):
        raise ValueError("residue/adaptive reduction requires standard backend, minfill, bits, and race=1")
    if reduction in ("graded", "graded-adaptive", "corridor", "corridor-adaptive") and window_radius is not None:
        raise ValueError("graded/corridor reduction cannot be combined with window_radius")
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
    if backend not in ("standard", "shared", "saturated", "euler", "shadow", "closure", "twist", "barcode", "fitting"):
        raise ValueError("backend must be standard, shared, saturated, euler, shadow, closure, twist, barcode, or fitting")
    if euler_max_states is not None and (type(euler_max_states) is not int or euler_max_states < 0):
        raise ValueError("euler_max_states must be a nonnegative integer or None")
    if shadow_max_work is not None and (type(shadow_max_work) is not int or shadow_max_work < 0):
        raise ValueError("shadow_max_work must be a nonnegative integer or None")
    if closure_max_work is not None and (type(closure_max_work) is not int or closure_max_work < 0):
        raise ValueError("closure_max_work must be a nonnegative integer or None")
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
        if use_rational and original.rational_source is not None:
            from .rational import montesinos_certificate
            e, tangles = original.rational_source
            witness = montesinos_certificate(e, tangles, check=check)
            check()
            evidence["montesinos"] = witness
            return Result(witness["status"], witness["method"], original.crossings,
                          diagram.crossings, monotonic() - start, evidence)
        if use_braid and original.braid_source is not None:
            strands, word = original.braid_source
            witness = braid_certificate(strands, word, backend=braid_backend,
                                        use_braid_reduction=False, check=check)
            check()
            evidence["braid"] = witness
            if witness["status"] != "INCONCLUSIVE":
                return Result(witness["status"], witness["method"], original.crossings,
                              diagram.crossings, monotonic() - start, evidence)
        if use_braid_profile and original.braid_source is not None:
            from .braid_profile import structural_word_certificate
            strands, word = original.braid_source
            witness = structural_word_certificate(strands, word, check=check)
            evidence["source_braid_structural"] = witness
            if witness["status"] != "INCONCLUSIVE":
                return Result(witness["status"], "source-" + witness["criterion"],
                              original.crossings, diagram.crossings,
                              monotonic() - start, evidence)
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
        if use_ranktwo and original.braid_source is not None:
            from .ranktwo import compress, verify
            strands, word = original.braid_source
            probe_start = monotonic()
            local_deadline = None if ranktwo_seconds is None else probe_start + ranktwo_seconds
            def ranktwo_check():
                check()
                if local_deadline is not None and monotonic() >= local_deadline:
                    raise ScanLimit("rank-two local time allowance exhausted")
            try:
                ranktwo_check()
                candidate = compress(strands, word, max_passes=1, dictionary="avl", check=ranktwo_check)
                reduced_word, replay = verify(strands, word, candidate["certificate"], check=ranktwo_check)
                ranktwo_check()
            except (ScanLimit, MemoryError) as exc:
                check()
                evidence["ranktwo"] = dict(status="skipped", reason=str(exc) or "memory allocation failed",
                                            seconds=monotonic()-probe_start)
            else:
                evidence["ranktwo"] = dict(status="verified", source_strands=strands,
                    source_word=list(word), certificate=candidate["certificate"],
                    statistics=candidate["stats"], replay=replay, seconds=monotonic()-probe_start,
                    used=len(reduced_word) < diagram.crossings)
                if len(reduced_word) < diagram.crossings:
                    # This new PD follows the source braid equality. Earlier PD
                    # simplification evidence describes a separate branch.
                    reduced_input = Diagram.from_braid(strands, reduced_word)
                    check()
                    restart_options.update(diagram=reduced_input, use_ranktwo=False,
                        seconds=None if deadline is None else max(0.0, deadline-monotonic()))
                    after = recognize(**restart_options)
                    check()
                    return Result(after.status, "ranktwo-"+after.method, original.crossings,
                                  after.reduced_crossings, monotonic()-start,
                                  dict(before_ranktwo=evidence, after_ranktwo=after.evidence))
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
        checked_modular = False
        if use_garside and original.braid_source is not None:
            # Keep the cheap modular obstruction first. Compression can avoid
            # the larger Jones scan, so leave that stage after the probe.
            # Reuse this check only on the unchanged whole diagram.
            if use_modular and use_alexander:
                witness = alexander_obstruction(diagram, check=check)
                check()
                if witness is not None:
                    evidence["alexander_modular"] = witness
                    return Result("KNOTTED", "alexander-modular", original.crossings,
                                  diagram.crossings, monotonic()-start, evidence)
                checked_modular = True
            from .garside_probe import propose
            proposal = propose(original, diagram.crossings, radius=garside_radius,
                               seconds=garside_seconds, max_ticks=garside_max_ticks,
                               max_targets=garside_max_targets, check=check)
            check()
            evidence["garside"] = proposal.evidence
            if proposal.candidate is not None:
                restart_options.update(diagram=proposal.candidate, use_garside=False,
                    seconds=None if deadline is None else max(0.0, deadline-monotonic()))
                after = recognize(**restart_options)
                check()
                return Result(after.status, "garside-"+after.method, original.crossings,
                              after.reduced_crossings, monotonic()-start,
                              dict(before_garside=evidence, after_garside=after.evidence))
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
                       r3_options=dict(r3_search=r3_search, r3_depth=r3_depth,
                                       r3_budget=r3_budget, r3_births=r3_births),
                       use_descending=use_descending,
                       jones_backend=jones_backend, potts_colors=potts_colors,
                       jones_max_states=jones_max_states, jones_max_transitions=jones_max_transitions,
                       max_objects=max_objects, deadline=deadline, check_d_squared=check_d_squared,
                       window_options=None if window_radius is None else dict(
                           radius=window_radius, max_objects=window_max_objects, seconds=window_seconds,
                           strategy=window_strategy),
                       scan_options=dict(pivot=pivot, algebra=algebra, tail=tail, race=race,
                                         race_after=race_after, backend=backend,
                                         euler_max_states=euler_max_states, composition=composition,
                                         shadow_max_work=shadow_max_work,
                                         closure_max_work=closure_max_work,
                                         composition_max_variables=composition_max_variables,
                                         twist_max_basis=twist_max_basis, reduction=reduction))
        method = "reduced-khovanov-F2-scan"
        check()
        if len(factors) == 1:
            # A retained source represents this whole knot across recorded
            # reductions. Never pass it to the individual factors below.
            source = original if original.braid_source is not None else None
            status, method = _decide_prime_looking(diagram, evidence, twist_source=source,
                                                   checked_modular=checked_modular, **options)
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
