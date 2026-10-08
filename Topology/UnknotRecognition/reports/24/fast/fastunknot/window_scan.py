"""Exact homological windows of the existing F2 Khovanov scanner.

Degrees are the scanner's raw cube degrees, before subtracting the number of
negative crossings.  To compute final degrees ``lower .. upper``, a prefix
with ``remaining`` crossings retains only

    lower - remaining - 1 <= degree <= upper + 1.

The two end degrees are guards for the incoming and outgoing differentials.
The suffix shifts degrees by an integer in ``0 .. remaining``.  Consequently
discarded objects cannot contribute to any final chain group in
``lower - 1 .. upper + 1``.  Subsequent unit cancellation is an actual chain
homotopy equivalence, which the remaining planar extension preserves.

Discarding takes place BEFORE allocation and transfer, not after an ordinary
scan has constructed the objects.  A resource limit applies to the objects
actually retained.  Only the requested final ranks are meaningful: guard
degrees may contain artificial homology introduced by brutal truncation.
"""
from __future__ import annotations

from time import monotonic
from math import isfinite

from .geometry import ScanLimit
from .ordering import best_scan_order, repeated_stages, validate_order
from .scan_fast import FastScan


class WindowScan(FastScan):
    """``FastScan`` with suffix-aware support and pre-allocation pruning."""

    def __init__(self, total_crossings: int, lower: int, upper: int,
                 max_objects: int | None = None, deadline: float | None = None,
                 shape_cache: bool = True, prune_isolated_guards: bool = True):
        if type(total_crossings) is not int or total_crossings < 0:
            raise ValueError("total_crossings must be a nonnegative integer")
        if type(lower) is not int or type(upper) is not int or lower > upper:
            raise ValueError("lower and upper must be integers with lower <= upper")
        super().__init__(max_objects=max_objects, deadline=deadline,
                         shape_cache=shape_cache)
        self.total_crossings = total_crossings
        self.lower, self.upper = lower, upper
        self.processed = 0
        self.prune_isolated_guards = prune_isolated_guards
        self.stats.update({
            "discarded_before_allocation": 0,
            "isolated_guard_objects_discarded": 0,
            "unpruned_prefix_stages": 0,
            "skipped_old_edge_smoothings": 0,
            "max_unfiltered_expansion_of_retained_prefix": 0,
            "window_profile": [],
        })
        if not lower - total_crossings - 1 <= 0 <= upper + 1:
            self.mid, self.deg, self.out, self.inc, self.live = [], [], [], [], 0

    def add_crossing(self, slots: tuple, reduce_now: bool = True) -> None:
        """Extend, brutally truncate, then optionally cancel unit entries."""
        self._check()
        if self.processed >= self.total_crossings:
            raise ValueError("more crossings than the declared total")
        remaining = self.total_crossings - self.processed - 1
        low, high = self.lower - remaining - 1, self.upper + 1
        # Every prefix object has raw degree in 0..processed+1.  When that
        # entire interval fits, there is no allocation or transfer to skip;
        # use the existing optimized kernel without per-edge window tests.
        if low <= 0 and high >= self.processed + 1:
            stats = self.stats
            old_entries = stats["entries"]
            old_max_after = stats["max_objects_after_elimination"]
            # Capture the allocated size before an adaptive reducer can compact
            # the object arrays. Its output may have fewer physical slots.
            super().add_crossing(slots, reduce_now=False)
            count = len(self.mid)
            if reduce_now:
                self.eliminate()
            self.processed += 1
            guard_discarded = self._discard_isolated_guards(remaining)
            stats["unpruned_prefix_stages"] += 1
            stats["max_unfiltered_expansion_of_retained_prefix"] = max(
                stats["max_unfiltered_expansion_of_retained_prefix"], count
            )
            if reduce_now:
                stats["max_objects_after_elimination"] = max(old_max_after, self.live)
            stats["window_profile"].append({
                "processed": self.processed,
                "remaining": remaining,
                "retained_lower": low,
                "retained_upper": high,
                "unfiltered_expansion_of_retained_prefix": count,
                "objects_before_elimination": count,
                "objects_after_elimination": self.live,
                "discarded_before_allocation": 0,
                "isolated_guard_objects_discarded": guard_discarded,
                "entries_before_elimination": stats["entries"] - old_entries,
            })
            return
        alg = self.algebra
        alg.stage(self.points, slots)
        self.composed = {}
        old_mid, old_deg, old_out = self.mid, self.deg, self.out
        glued = {}
        for ma in set(old_mid):
            if ma is not None:
                nm0, closed0, _ = alg.glue(ma, 0)
                nm1, closed1, _ = alg.glue(ma, 1)
                glued[ma] = (nm0, 1 << closed0, nm1, 1 << closed1)

        # Test the retained object count before constructing object/edge arrays.
        # ``unfiltered`` refers to this retained prefix, not a full-scan run.
        count = unfiltered = 0
        for o, ma in enumerate(old_mid):
            if ma is None:
                continue
            _, k0, _, k1 = glued[ma]
            unfiltered += k0 + k1
            h = old_deg[o]
            if low <= h <= high:
                count += k0
            if low <= h + 1 <= high:
                count += k1
        if self.max_objects is not None and count > self.max_objects:
            raise ScanLimit(
                f"{count} retained objects would exceed the ceiling {self.max_objects}"
            )

        mid, deg = [], []
        base = [None] * len(old_mid)
        for o, ma in enumerate(old_mid):
            if ma is None:
                continue
            nm0, k0, nm1, k1 = glued[ma]
            h = old_deg[o]
            b0 = b1 = None
            if low <= h <= high:
                b0 = len(mid)
                mid.extend([nm0] * k0)
                deg.extend([h] * k0)
            if low <= h + 1 <= high:
                b1 = len(mid)
                mid.extend([nm1] * k1)
                deg.extend([h + 1] * k1)
            base[o] = (b0, b1)
        out = [{} for _ in range(count)]
        inc = [set() for _ in range(count)]
        saddles, transfers = {}, {}
        shared = alg.shape_results if alg.stats["shape_hits"] else None
        deadline = self.deadline if self.hook is None else 0.0
        skipped = 0
        for o, ma in enumerate(old_mid):
            if ma is None:
                continue
            if deadline is not None and not o & 511:
                self._check()
            b0, b1 = base[o]
            if b0 is not None and b1 is not None:
                entries = saddles.get(ma)
                if entries is None:
                    entries = saddles[ma] = alg.transfer(ma, ma, 1, 0, 1)
                for ls, lt, value in entries:
                    out[b0 + ls][b1 + lt] = value
                    inc[b1 + lt].add(b0 + ls)
            for o2, f in old_out[o].items():
                c0, c1 = base[o2]
                needed0 = b0 is not None and c0 is not None
                needed1 = b1 is not None and c1 is not None
                skipped += 2 - needed0 - needed1
                if not needed0 and not needed1:
                    continue
                mb = old_mid[o2]
                for i, needed, source, target in (
                    (0, needed0, b0, c0), (1, needed1, b1, c1)
                ):
                    if not needed:
                        continue
                    key = (ma, mb, f, i)
                    entries = transfers.get(key)
                    if entries is None:
                        if shared is None:
                            entries = alg.transfer(ma, mb, f, i, i)
                        else:
                            # Distinct tag: ordinary FastScan caches both
                            # smoothings together under a different key shape.
                            shape_key = (
                                "window-transfer", alg.shape(ma), alg.shape(mb),
                                alg.shape_slots, f, i,
                            )
                            entries = shared.get(shape_key)
                            if entries is None:
                                entries = shared[shape_key] = alg.transfer(
                                    ma, mb, f, i, i
                                )
                            else:
                                alg.stats["result_hits"] += 1
                        transfers[key] = entries
                    for ls, lt, value in entries:
                        out[source + ls][target + lt] = value
                        inc[target + lt].add(source + ls)

        self.mid, self.deg, self.out, self.inc, self.live = mid, deg, out, inc, count
        self.points = alg.new_points()
        self.processed += 1
        stats = self.stats
        entries = sum(map(len, out))
        stats["entries"] += entries
        stats["discarded_before_allocation"] += unfiltered - count
        stats["skipped_old_edge_smoothings"] += skipped
        stats["max_unfiltered_expansion_of_retained_prefix"] = max(
            stats["max_unfiltered_expansion_of_retained_prefix"], unfiltered
        )
        stats["max_objects_before_elimination"] = max(
            stats["max_objects_before_elimination"], count
        )
        stats["max_boundary"] = max(stats["max_boundary"], len(self.points))
        if reduce_now:
            self.eliminate()
        guard_discarded = self._discard_isolated_guards(remaining)
        if reduce_now:
            stats["max_objects_after_elimination"] = max(
                stats["max_objects_after_elimination"], self.live
            )
        stats["window_profile"].append({
            "processed": self.processed,
            "remaining": remaining,
            "retained_lower": low,
            "retained_upper": high,
            "unfiltered_expansion_of_retained_prefix": unfiltered,
            "objects_before_elimination": count,
            "objects_after_elimination": self.live,
            "discarded_before_allocation": unfiltered - count,
            "isolated_guard_objects_discarded": guard_discarded,
            "entries_before_elimination": entries,
        })

    def _discard_isolated_guards(self, remaining: int) -> int:
        """Drop independent summands whose continuation misses every target.

        A nonisolated guard is needed for an incident differential and MUST
        stay.  An isolated degree-h object is a direct summand; all of its
        continued degrees lie in [h, h+remaining].  If this interval misses
        [lower, upper], this summand cannot affect any requested homology.
        """
        if not self.prune_isolated_guards:
            return 0
        count = 0
        for o, ma in enumerate(self.mid):
            if ma is None or self.out[o] or self.inc[o]:
                continue
            h = self.deg[o]
            if h > self.upper or h + remaining < self.lower:
                self.mid[o] = self.out[o] = self.inc[o] = None
                count += 1
        self.live -= count
        self.stats["isolated_guard_objects_discarded"] += count
        return count

    def requested_ranks(self) -> dict[int, int]:
        """Return only target ranks; homology in guard degrees is artificial."""
        if self.processed != self.total_crossings or self.points:
            raise ValueError("the declared diagram is not closed yet")
        if any(self.out):
            raise ArithmeticError("requested_ranks requires complete elimination")
        return {
            h: dim for h, dim in self.ranks_by_degree().items()
            if self.lower <= h <= self.upper
        }


def validate_seconds(seconds):
    if seconds is not None and (type(seconds) not in (int, float)
                                or not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative, or None")


def khovanov_window(pd, lower: int, upper: int, *, order=None, max_objects=None,
                    seconds=None, check_d_squared=False, shape_cache=None,
                    prune_isolated_guards=True, reduction="standard",
                    composition="standard", composition_max_variables=18) -> dict:
    """Exact F2 unreduced ranks in requested raw degrees of a validated PD.

    The returned ``window_rank`` is the sum of ONLY the requested ranks.  It
    is not the total Khovanov rank.  In particular, a two-dimensional window
    is not an unknot certificate unless it covers all raw degrees ``0..n``.
    A resource limit raises ``ScanLimit`` instead of returning a verdict.
    """
    validate_seconds(seconds)
    deadline = None if seconds is None else monotonic() + seconds
    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted")
    if reduction not in ("standard", "residue", "adaptive"):
        raise ValueError("reduction must be standard, residue, or adaptive")
    if composition not in ("standard", "component", "component-dense"):
        raise ValueError("composition must be standard, component, or component-dense")
    if type(composition_max_variables) is not int or composition_max_variables < 0:
        raise ValueError("composition_max_variables must be nonnegative")
    pd = [tuple(c) for c in pd]
    if type(lower) is not int or type(upper) is not int or lower > upper:
        raise ValueError("lower and upper must be integers with lower <= upper")
    if order is not None:
        order = validate_order(len(pd), order)
    if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
        raise ValueError("max_objects must be a nonnegative integer")
    if not pd:
        by_degree = {0: 2} if lower <= 0 <= upper else {}
        return {
            "window_rank": sum(by_degree.values()), "by_degree": by_degree,
            "raw_lower": lower, "raw_upper": upper,
            "complete_rank": lower <= 0 <= upper,
            "stats": {}, "order": [],
        }
    check()
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12), check=check)
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan_type = WindowScan
    if reduction != "standard":
        from .residue import AdaptiveScan, ResidueScan
        reducer = AdaptiveScan if reduction == "adaptive" else ResidueScan
        # WindowScan supplies pruning; the reducer supplies cancellation and
        # its counters. Cooperative super() calls initialize one FastScan.
        scan_type = type("ReducedWindowScan", (WindowScan, reducer), {})
    complex_ = scan_type(
        len(pd), lower, upper, max_objects=max_objects,
        deadline=deadline, shape_cache=shape_cache,
        prune_isolated_guards=prune_isolated_guards,
    )
    if composition != "standard":
        from .component_algebra import install_on_empty_scan
        # A disjoint initial window has no objects; its answer is already zero.
        if complex_.live:
            install_on_empty_scan(complex_, minimum_pairs=0 if composition == "component-dense" else 64,
                                  method="fast" if composition == "component-dense" else "auto",
                                  dense_limit=composition_max_variables)
    for index in order:
        complex_.add_crossing(pd[index])
        if check_d_squared:
            complex_.check_d_squared()
    by_degree = complex_.requested_ranks()
    stats = dict(complex_.stats)
    stats.update(complex_.algebra.stats)
    result = {
        "window_rank": sum(by_degree.values()), "by_degree": by_degree,
        "raw_lower": lower, "raw_upper": upper,
        "complete_rank": lower <= 0 and upper >= len(pd),
        "stats": stats, "order": order,
    }
    result["reduction"] = reduction
    result["composition"] = composition
    if hasattr(complex_.algebra, "kernel_stats"):
        result["composition_stats"] = dict(complex_.algebra.kernel_stats)
    return result

