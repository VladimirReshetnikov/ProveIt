"""Bounded adaptive homological-window probes before a complete backend.

A successful partial query is exact on its interval, but agreement with the
unknot there is inconclusive. Widening restarts because discarded groups cannot
be recovered from a narrow scan. All attempts share one optional time budget.
"""
from time import monotonic

from .geometry import ScanLimit
from .window_bounds import khovanov_window_auto
from .window_scan import validate_seconds


def window_radii(maximum):
    """0, 1, 2, 4, ..., with the requested endpoint included once."""
    yield 0
    radius = 1
    while radius < maximum:
        yield radius
        radius *= 2
    if maximum:
        yield maximum


def probe_windows(diagram, *, maximum_radius, max_objects=20000, seconds=0.1,
                  deadline=None, order=None, check_d_squared=False,
                  reduction="standard", composition="standard", composition_max_variables=18, strategy="support"):
    if type(maximum_radius) is not int or maximum_radius < 0:
        raise ValueError("maximum_radius must be a nonnegative integer")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
        raise ValueError("max_objects must be a nonnegative integer or None")
    validate_seconds(seconds)
    if strategy not in ("support", "minimal"):
        raise ValueError("window strategy must be support or minimal")
    query = khovanov_window_auto
    if strategy == "minimal":
        from .minimal_window import khovanov_minimal_window_auto
        query = khovanov_minimal_window_auto
    started = monotonic()
    stop = None if seconds is None else started + seconds
    if deadline is not None:
        stop = deadline if stop is None else min(stop, deadline)
    negative = diagram.signs().count(-1)
    maximum = min(maximum_radius, max(negative, diagram.crossings - negative))
    evidence = dict(status="INCONCLUSIVE", field="F2", diagram_pd=[list(row) for row in diagram.pd],
                    negative_crossings=negative, maximum_radius=maximum, attempts=[],
                    policy="geometric radii, shared budget, restart when widening", strategy=strategy)
    result = dict(status="INCONCLUSIVE", evidence=evidence, order=order)
    for radius in window_radii(maximum):
        before = monotonic()
        if deadline is not None and before >= deadline:
            raise ScanLimit("time budget exhausted")
        if stop is not None and before >= stop:
            evidence["stop_reason"] = "window time budget exhausted"
            break
        remaining = None if stop is None else max(0.0, stop - before)
        try:
            window = query(diagram, negative - radius, negative + radius,
                order=result["order"], max_objects=max_objects, seconds=remaining,
                check_d_squared=check_d_squared, reduction=reduction,
                composition=composition, composition_max_variables=composition_max_variables)
        except (ScanLimit, MemoryError) as exc:
            evidence["attempts"].append(dict(radius=radius, status="resource-limit",
                                              reason=str(exc) or "memory allocation failed"))
            evidence["stop_reason"] = "window resource limit; continue complete backend"
            if deadline is not None and monotonic() >= deadline:
                raise ScanLimit("time budget exhausted") from exc
            break
        after = monotonic()
        if deadline is not None and after >= deadline:
            raise ScanLimit("time budget exhausted")
        result["order"] = window["order"]
        ranks = {h - negative: count for h, count in window["by_degree"].items()}
        attempt = dict(radius=radius, status="INCONCLUSIVE", seconds=after - before,
                       unreduced_rank_by_normalized_degree=ranks, complete_rank=window["complete_rank"],
                       raw_lower=window["raw_lower"], raw_upper=window["raw_upper"],
                       orientation=window["orientation"],
                       profile_degree_convention=window["profile_degree_convention"],
                       scan_order=window["order"], scan_stats=window["stats"])
        if "nice_order" in window:
            attempt["nice_order"] = window["nice_order"]
            attempt["binomial_bound_certified"] = window["binomial_bound_certified"]
        evidence["attempts"].append(attempt)
        if ranks != {0: 2}:
            result["status"] = evidence["status"] = attempt["status"] = "KNOTTED"
            break
        if window["complete_rank"]:
            result["status"] = evidence["status"] = attempt["status"] = "UNKNOT"
            break
        if radius == maximum:
            evidence["stop_reason"] = "maximum radius reached with agreeing partial homology"
        elif stop is not None and 2 * (after - before) > stop - after:
            evidence["stop_reason"] = "remaining budget is less than twice the last query time"
            break
    evidence["seconds"] = monotonic() - started
    return result
