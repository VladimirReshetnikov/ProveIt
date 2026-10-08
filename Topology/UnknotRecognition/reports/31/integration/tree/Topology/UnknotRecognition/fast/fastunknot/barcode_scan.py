"""Exact interval decomposition for a restricted class of open scan summands.

If every object of a differential-graph component has one matching M and every
nonzero entry is one fixed nonunit theta in End(M), write d_h = theta B_h with
B_h a binary matrix.  End(M) is the commutative F2 algebra with square-zero dot
generators, so theta**2 = 0.  The binary matrices constitute a representation of
a linearly oriented type-A quiver; no equation B_(h+1) B_h = 0 is required.
Its interval decomposition induces an exact chain isomorphism over End(M).

This module computes interval multiplicities from ranks of binary matrix
products.  It then reconstructs the interval complexes before applying the
existing literal component-sharing pass.  It does not claim to recognize all
isomorphic complexes, and does not identify entries by hashes alone.
"""
from __future__ import annotations

from collections import defaultdict
from time import monotonic

from .component_scan import ComponentScan, components
from .ordering import best_scan_order, repeated_stages, validate_order
from .window_scan import validate_seconds
from .geometry import ScanLimit


def _binary_basis(vectors, check=None):
    """A basis of the span, in the original binary coordinates."""
    pivots = {}
    for index, vector in enumerate(vectors):
        if check is not None and not index & 255:
            check()
        while vector:
            top = vector.bit_length() - 1
            if top not in pivots:
                pivots[top] = vector
                break
            vector ^= pivots[top]
    return list(pivots.values())


def _apply(columns, vector):
    """Apply a column-packed binary matrix to a binary column vector."""
    result = 0
    while vector:
        low = vector & -vector
        result ^= columns[low.bit_length() - 1]
        vector ^= low
    return result


def interval_multiplicities(dimensions, arrows, check=None):
    """Return (intervals, ranks) for a finite binary type-A representation.

    ``dimensions[h]`` is dim V_h. ``arrows[h]`` is a sequence of that many
    column-packed integers for V_h -> V_(h+1).  An interval is (a,b,copies),
    inclusive at both ends, with copies positive.  ``ranks[(i,j)]`` is the
    rank of B_(j-1)...B_i, and ranks[(i,i)] = dim V_i.

    Basis vectors of successive image spaces suffice; full matrix products
    and basis-change witnesses are not stored.  All output is exact.
    """
    dimensions = list(dimensions)
    arrows = [list(columns) for columns in arrows]
    length = len(dimensions)
    if any(type(d) is not int or d < 0 for d in dimensions):
        raise ValueError("quiver dimensions must be nonnegative integers")
    if len(arrows) != max(0, length - 1):
        raise ValueError("one arrow is required between adjacent layers")
    for h, columns in enumerate(arrows):
        if len(columns) != dimensions[h]:
            raise ValueError("the matrix column count does not match its source")
        if any(type(v) is not int or v < 0 or v.bit_length() > dimensions[h + 1]
               for v in columns):
            raise ValueError("a matrix column is outside its target space")
    ranks = {}
    for i, dimension in enumerate(dimensions):
        if check is not None:
            check()
        ranks[i, i] = dimension
        image = [1 << j for j in range(dimension)]
        for j in range(i + 1, length):
            image = _binary_basis((_apply(arrows[j - 1], v) for v in image), check)
            ranks[i, j] = len(image)
            if not image:
                for k in range(j + 1, length):
                    ranks[i, k] = 0
                break
    intervals = []
    for a in range(length):
        for b in range(a, length):
            copies = (ranks[a, b] - ranks.get((a - 1, b), 0)
                      - ranks.get((a, b + 1), 0) + ranks.get((a - 1, b + 1), 0))
            if copies < 0:
                raise ArithmeticError("a quiver interval has negative multiplicity")
            if copies:
                intervals.append((a, b, copies))
    if sum((b - a + 1) * copies for a, b, copies in intervals) != sum(dimensions):
        raise ArithmeticError("interval decomposition changed the total dimension")
    return intervals, ranks


def _eligible_data(scan, group):
    """Return matching, theta, first degree, layer matrices; else None."""
    matching = scan.mid[group[0]]
    theta = None
    for v in group:
        if scan.mid[v] != matching:
            return None
        for w, value in scan.out[v].items():
            if not value or value & 1:
                return None                  # a nonzero common radical entry is required
            if theta is None:
                theta = value
            elif value != theta:
                return None
            if scan.deg[w] != scan.deg[v] + 1:
                raise ArithmeticError("a differential does not raise degree by one")
    if theta is None:
        return None                          # existing sharing already handles a singleton
    first, last = min(scan.deg[v] for v in group), max(scan.deg[v] for v in group)
    layers = [[] for _ in range(last - first + 1)]
    for v in group:
        layers[scan.deg[v] - first].append(v)
    dimensions = list(map(len, layers))
    arrows = []
    for h, sources in enumerate(layers[:-1]):
        target_index = {v: i for i, v in enumerate(layers[h + 1])}
        arrows.append([sum(1 << target_index[w] for w in scan.out[v]) for v in sources])
    return matching, theta, first, dimensions, arrows


class BarcodeScan(ComponentScan):
    """ComponentScan with exact common-nilpotent interval normalization.

    ``barcode_max_objects`` bounds the size of a component on which the extra
    normalization is attempted.  Skipped components retain the complete exact
    scanner representation.  The default has no extra component-size limit.

    ``length_cap`` is None for exact interval lengths. With rank_cap=3 it may
    be 3 for arbitrary additive square-zero-action suffixes, or 2 when every
    final closure of a nonempty matching has even Euler characteristic, as
    happens for this scanner's ordinary Khovanov closures. These replacements
    preserve capped final rank, not homotopy type.
    """

    def __init__(self, *args, barcode_max_objects=None, length_cap=None, **kwargs):
        super().__init__(*args, **kwargs)
        if barcode_max_objects is not None and (type(barcode_max_objects) is not int
                                               or barcode_max_objects < 0):
            raise ValueError("barcode_max_objects must be nonnegative or None")
        self.barcode_max_objects = barcode_max_objects
        if length_cap is not None and (type(length_cap) is not int or length_cap not in (2, 3)
                                       or self.rank_cap != 3):
            raise ValueError("length_cap 2 or 3 is supported only with rank_cap=3")
        self.length_cap = length_cap
        self.stats.update(barcode_components=0, barcode_intervals=0, barcode_splits=0,
                          barcode_normalized_objects=0, barcode_skipped_size=0,
                          barcode_rank_queries=0, barcode_truncated_intervals=0,
                          barcode_removed_objects=0, interval_checkpoint_count=1,
                          max_checkpoint_gap=0, current_checkpoint_gap=0,
                          max_checkpoint_representatives=1, max_checkpoint_types=1)
        self._last_checkpoint_stage = 0
        if length_cap is not None:
            # Once a long interval is shortened, we represent a decision-equivalent
            # model, not an isomorphic literal expansion of the original complex.
            self.stats["max_weighted_decision_model_objects"] = self.stats.pop(
                "max_expanded_after_elimination_lower_bound")

    def _compress(self, ancestry, groups=None):
        # Inspect the graph first. In the common ineligible case, reuse this
        # inventory and let the inherited sharing pass see the original arrays.
        groups = list(components(self)) if groups is None else list(groups)
        eligible = []
        unclassified_components = unclassified_objects = 0
        for group in groups:
            self._check()
            limit = self.barcode_max_objects
            if limit is not None and len(group) > limit:
                self.stats["barcode_skipped_size"] += 1
                data = None
            else:
                data = _eligible_data(self, group) if len(group) > 1 else None
            eligible.append(data)
            if data is None and len(group) > 1:
                unclassified_components += 1
                unclassified_objects += len(group)
        if not any(data is not None for data in eligible):
            self._finish_compression(ancestry, groups, unclassified_components,
                                     unclassified_objects)
            return

        old_mid, old_deg, old_out = self.mid, self.deg, self.out
        mid, degree, out, origin = [], [], [], []
        removed = 0
        for group, data in zip(groups, eligible):
            parent = ancestry[group[0]]
            if any(ancestry[v] != parent for v in group):
                raise ArithmeticError("a differential joined independent parent summands")
            if data is None:
                offset = len(mid)
                local = {v: offset + i for i, v in enumerate(group)}
                for v in group:
                    mid.append(old_mid[v])
                    degree.append(old_deg[v])
                    out.append({local[w]: value for w, value in old_out[v].items()})
                    origin.append(parent)
                continue
            matching, theta, first, dimensions, arrows = data
            intervals, ranks = interval_multiplicities(dimensions, arrows, self._check)
            interval_count = sum(copies for _, _, copies in intervals)
            self.stats["barcode_components"] += 1
            self.stats["barcode_intervals"] += interval_count
            self.stats["barcode_splits"] += interval_count - 1
            self.stats["barcode_normalized_objects"] += len(group)
            self.stats["barcode_rank_queries"] += len(ranks)
            for a, b, copies in intervals:
                end = b if self.length_cap is None else min(b, a + self.length_cap - 1)
                if end < b:
                    removed += (b - end) * copies
                    self.stats["barcode_truncated_intervals"] += copies
                for _ in range(copies):
                    for h in range(a, end + 1):
                        v = len(mid)
                        mid.append(matching)
                        degree.append(first + h)
                        out.append({v + 1: theta} if h < end else {})
                        origin.append(parent)
        inc = [set() for _ in mid]
        for v, row in enumerate(out):
            for w in row:
                inc[w].add(v)
        if len(mid) != self.live - removed:
            raise ArithmeticError("interval normalization changed the object count")
        self.stats["barcode_removed_objects"] += removed
        self.mid, self.deg, self.out, self.inc, self.live = mid, degree, out, inc, len(mid)
        self._finish_compression(origin, None, unclassified_components, unclassified_objects)

    def _finish_compression(self, ancestry, groups, unclassified_components,
                            unclassified_objects):
        if self.length_cap is not None:
            self.stats["max_expanded_after_elimination_lower_bound"] = self.stats[
                "max_weighted_decision_model_objects"]
        super()._compress(ancestry, groups=groups)
        if self.length_cap is not None:
            self.stats["max_weighted_decision_model_objects"] = self.stats.pop(
                "max_expanded_after_elimination_lower_bound")
            row = self.stage_history[-1]
            row["weighted_decision_model_objects"] = row.pop("expanded_objects")
            row.pop("expanded_objects_is_lower_bound")
            row["multiplicities_capped"] = True
            row["decision_equivalence_only"] = True
        row = self.stage_history[-1]
        stage = row['stage']
        gap = stage - self._last_checkpoint_stage
        checkpoint = unclassified_components == 0
        row.update(interval_checkpoint=checkpoint,
                   unclassified_components=unclassified_components,
                   unclassified_objects=unclassified_objects,
                   frontier_points=len(self.points), checkpoint_gap=gap)
        self.stats['max_checkpoint_gap'] = max(self.stats['max_checkpoint_gap'], gap)
        if checkpoint:
            self._last_checkpoint_stage = stage
            self.stats['interval_checkpoint_count'] += 1
            self.stats['max_checkpoint_representatives'] = max(
                self.stats['max_checkpoint_representatives'], self.live)
            self.stats['max_checkpoint_types'] = max(
                self.stats['max_checkpoint_types'], len(self.weights))
        self.stats['current_checkpoint_gap'] = stage - self._last_checkpoint_stage


def _barcode_scan(pd, *, order=None, max_objects=None, seconds=None,
                  check_d_squared=False, shape_cache=None, rank_cap=None,
                  barcode_max_objects=None, length_cap=None):
    validate_seconds(seconds)
    deadline = None if seconds is None else monotonic() + seconds
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
        raise ValueError("max_objects must be nonnegative or None")
    pd = [tuple(crossing) for crossing in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        scan = BarcodeScan(max_objects=max_objects, deadline=deadline, shape_cache=shape_cache,
                           rank_cap=rank_cap, barcode_max_objects=barcode_max_objects,
                           length_cap=length_cap)
        return None, []
    check()
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12), check=check)
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan = BarcodeScan(max_objects=max_objects, deadline=deadline, shape_cache=shape_cache,
                       rank_cap=rank_cap, barcode_max_objects=barcode_max_objects,
                       length_cap=length_cap)
    for index in order:
        scan.add_crossing(pd[index])
        if check_d_squared:
            scan.check_d_squared()
    return scan, order


def barcode_khovanov_rank(pd, *, order=None, max_objects=None, seconds=None,
                           check_d_squared=False, shape_cache=None,
                           barcode_max_objects=None):
    """Exact ungraded F2 rank and raw homological grading of a validated knot."""
    scan, order = _barcode_scan(pd, order=order, max_objects=max_objects, seconds=seconds,
                               check_d_squared=check_d_squared, shape_cache=shape_cache,
                               barcode_max_objects=barcode_max_objects)
    if scan is None:
        return dict(rank=2, reduced_rank=1, by_degree={0: 2}, stats={}, order=[],
                    backend="nilpotent-interval-sharing", stages=[])
    rank = scan.total_rank()
    if rank % 2:
        raise ArithmeticError("odd unreduced F2 rank for a knot")
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(rank=rank, reduced_rank=rank // 2, by_degree=scan.ranks_by_degree(),
                stats=stats, order=order, backend="nilpotent-interval-sharing",
                stages=scan.stage_history)


def barcode_khovanov_decide(pd, *, order=None, max_objects=None, seconds=None,
                             check_d_squared=False, shape_cache=None,
                             barcode_max_objects=None, length_cap=2):
    """Exact unknot decision with interval sharing and rank cap three.

    With the default length_cap=2, intervals longer than two are replaced by
    length-two intervals.  Every ordinary closure of a nonempty matching has
    even chain-space dimensions, so this preserves the final rank capped at
    three. It need not preserve exact rank, homology, or chain homotopy type.
    length_cap=3 is also valid without that evenness property; length_cap=None
    retains exact interval lengths.  The diagram MUST already be validated
    as a classical one-component knot.
    Resource exhaustion raises ScanLimit; it is never a mathematical verdict.
    """
    scan, order = _barcode_scan(pd, order=order, max_objects=max_objects, seconds=seconds,
                               check_d_squared=check_d_squared, shape_cache=shape_cache,
                               rank_cap=3, barcode_max_objects=barcode_max_objects,
                               length_cap=length_cap)
    if scan is None:
        return dict(status="UNKNOT", rank_capped=2, rank_cap=3, stats={}, order=[],
                    backend="nilpotent-interval-sharing-saturated", length_cap=length_cap,
                    stages=[])
    capped = scan.total_rank()
    if capped not in (2, 3):
        raise ArithmeticError("a validated knot must have unreduced rank at least two")
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(status="UNKNOT" if capped == 2 else "KNOTTED", rank_capped=capped,
                rank_cap=3, stats=stats, order=order,
                backend="nilpotent-interval-sharing-saturated", length_cap=length_cap,
                stages=scan.stage_history)
