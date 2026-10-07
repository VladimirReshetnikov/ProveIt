"""Experimental pointed scanner: cut one edge and set its endpoint dot to zero.

The underlying geometry remains Planar's, while monomials omit circle zero,
the circle containing the distinguished (smallest labelled) cut endpoint.
Cross-stage topology plans are ordinary unpointed plans. Numerical shape
results are cleared whenever the marked-input convention changes.
"""
from collections import defaultdict
from time import monotonic

from .planar import Planar
from .scan_fast import FastScan
from .ordering import best_scan_order, repeated_stages, validate_order


def pointed_component(c, input_shift=1):
    left, right, boundary, extra, _ = c
    rest = boundary >> 1
    choices = []
    while rest:
        low = rest & -rest
        choices.append((boundary >> 1) ^ low)
        rest ^= low
    return (left >> input_shift, right >> input_shift, boundary >> 1, extra,
            bool(boundary & 1), tuple(choices))


def evaluate_pointed(components, f, g=0):
    result = 1
    for left, right, boundary, extra, marked, choices in components:
        dots = (f & left).bit_count() + (g & right).bit_count() + extra
        if marked:
            if dots:
                return 0
            result <<= boundary
        elif dots >= 2:
            return 0
        elif dots:
            result <<= boundary
        elif not boundary:
            return 0
        else:
            nxt = 0
            for choice in choices:
                nxt ^= result << choice
            result = nxt
    return result


class ReducedPlanar(Planar):
    def __init__(self, marked_endpoint, shape_cache=True):
        self.marked_endpoint = marked_endpoint
        self.marked_mode = None
        super().__init__(shape_cache=shape_cache)

    def stage(self, points, slots):
        super().stage(points, slots)
        self.pointed_compositions = {}
        self.pointed_transfers = {}
        self.marked_before = self.marked_endpoint in points
        self.marked_after = self.marked_before or self.marked_endpoint in slots
        mode = (self.marked_before, self.marked_after)
        if mode != self.marked_mode:
            self.shape_results.clear()
            self.marked_mode = mode

    def compose(self, a, b, c, f, g):
        if not self.marked_after:
            return super().compose(a, b, c, f, g)
        key = (a, b, c)
        found = self.pointed_compositions.get(key)
        if found is None:
            ordinary = super().compose_plan(a, b, c)
            if ordinary is None:
                return 0
            found = (tuple(pointed_component(x) for x in ordinary[0]), {})
            self.pointed_compositions[key] = found
        components, memo = found
        result = 0
        fs = []
        while f:
            low = f & -f
            fs.append(low.bit_length() - 1)
            f ^= low
        while g:
            low = g & -g
            tg = low.bit_length() - 1
            g ^= low
            for tf in fs:
                pair = (tf, tg)
                value = memo.get(pair)
                if value is None:
                    value = memo[pair] = evaluate_pointed(components, tf, tg)
                result ^= value
        return result

    def transfer(self, a, b, f, i_src, i_tgt):
        if not self.marked_after:
            return super().transfer(a, b, f, i_src, i_tgt)
        key = (a, b, i_src, i_tgt)
        found = self.pointed_transfers.get(key)
        if found is None:
            raw, touched_mask, renumber, _ = super().transfer_plan(a, b, i_src, i_tgt)
            shift = int(self.marked_before)
            plans = tuple((ls, lt, tuple(pointed_component(x, shift) for x in components))
                          for ls, lt, components in raw)
            renumber = {old >> shift: new >> 1 for old, new in renumber.items()
                        if not (shift and old == 1)}
            found = (plans, touched_mask >> shift, renumber, {})
            self.pointed_transfers[key] = found
        plans, touched_mask, renumber, memo = found
        if not plans:
            return ()
        total = [0] * len(plans)
        while f:
            low = f & -f
            monomial = low.bit_length() - 1
            f ^= low
            core = monomial & touched_mask
            values = memo.get(core)
            if values is None:
                values = memo[core] = [evaluate_pointed(components, core)
                                     for _, _, components in plans]
            rest = monomial ^ core
            shift = 0
            while rest:
                low = rest & -rest
                shift |= renumber[low]
                rest ^= low
            for t, value in enumerate(values):
                total[t] ^= value << shift
        return tuple((plan[0], plan[1], value)
                     for plan, value in zip(plans, total) if value)


class ReducedScan(FastScan):
    def __init__(self, marked_endpoint, max_objects=None, deadline=None, shape_cache=True):
        super().__init__(max_objects=max_objects, deadline=deadline, shape_cache=False)
        self.algebra = ReducedPlanar(marked_endpoint, shape_cache=shape_cache)


def cut_edge(pd, order, edge=None):
    """Cut an edge at the last crossing; no extra frontier until the final stage.

    Among its four edges choose the one whose first occurrence is earliest,
    so the reduced quotient is active through the longest possible suffix.
    An explicit edge allows experiments with other locations.
    """
    if not pd:
        return [], (), None
    if edge is None:
        position = {index: k for k, index in enumerate(order)}
        first = {label: len(pd) for label in pd[order[-1]]}
        for i, row in enumerate(pd):
            for label in row:
                if label in first:
                    first[label] = min(first[label], position[i])
        edge = min(first, key=lambda label: (first[label], label))
    least = min(x for row in pd for x in row)
    ends = (least - 2, least - 1)
    cut = [list(row) for row in pd]
    occurrences = [(i, j) for i in order for j, label in enumerate(pd[i]) if label == edge]
    if len(occurrences) != 2:
        raise ValueError("the marked edge must have two ends")
    for (i, j), endpoint in zip(occurrences, ends):
        cut[i][j] = endpoint
    return [tuple(row) for row in cut], ends, edge


def _prepare_scan(pd, order, edge, max_objects, seconds, shape_cache):
    pd = [tuple(row) for row in pd]
    deadline = None if seconds is None else monotonic() + seconds
    order = best_scan_order(pd, tries=min(len(pd), 12)) if order is None else validate_order(len(pd), order)
    cut, endpoints, edge = cut_edge(pd, order, edge=edge)
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(cut, order) >= len(order)
    scan = ReducedScan(endpoints[0], max_objects=max_objects, deadline=deadline,
                       shape_cache=shape_cache)
    return pd, order, cut, endpoints, edge, scan


def _terminal_rank(scan, endpoints):
    if scan.points != frozenset(endpoints):
        raise ArithmeticError("cut scan did not end in its two endpoints")
    if any(row for row in scan.out if row is not None):
        raise ArithmeticError("reduced terminal complex has nonzero differential")
    if scan.live <= 0 or not scan.live & 1:
        raise ArithmeticError("a knot must have positive odd reduced F2 rank")
    by_degree = defaultdict(int)
    for ma, h in zip(scan.mid, scan.deg):
        if ma is not None:
            by_degree[h] += 1
    return dict(sorted(by_degree.items()))


def reduced_khovanov_rank(pd, *, order=None, edge=None, max_objects=None, seconds=None,
                          check_d_squared=False, shape_cache=None):
    """Compute reduced F2 Khovanov homology of a validated one-component PD.

    Unlike ``khovanov_rank``, this API's ``rank`` and ``by_degree`` describe the
    reduced complex directly.  Degrees use the same unnormalized cube convention.
    A basepoint at the last scanned crossing keeps the original frontier width
    before closure.  An explicit ``edge`` overrides that performance policy.
    Limits raise ScanLimit; exhausting a budget never gives a knot verdict.
    """
    pd = [tuple(row) for row in pd]
    if not pd:
        return {"rank": 1, "reduced_rank": 1, "by_degree": {0: 1}, "stats": {},
                "order": [], "method": "pointed-khovanov-F2-scan"}
    pd, order, cut, endpoints, edge, scan = _prepare_scan(
        pd, order, edge, max_objects, seconds, shape_cache)
    for i in order:
        scan.add_crossing(cut[i])
        if check_d_squared:
            scan.check_d_squared()
    by_degree = _terminal_rank(scan, endpoints)
    return {"rank": scan.live, "reduced_rank": scan.live, "by_degree": by_degree,
            "stats": dict(scan.stats, **scan.algebra.stats), "order": order,
            "marked_edge": edge, "method": "pointed-khovanov-F2-scan"}


def _isolated_summands(scan, count=2):
    found = []
    for ident, ma in enumerate(scan.mid):
        if not ident & 511:
            scan._check()
        if ma is not None and not scan.out[ident] and not scan.inc[ident]:
            found.append({"object_id": ident, "homological_degree": scan.deg[ident],
                          "matching": [list(pair) for pair in scan.algebra.pairs[ma]]})
            if len(found) >= count:
                break
    return found


def reduced_khovanov_decision(pd, *, order=None, edge=None, max_objects=None, seconds=None,
                              check_d_squared=False, shape_cache=None, early_stop=True):
    """Decide unknotness, optionally stopping on two isolated direct summands.

    Each isolated matching summand, after gluing the remaining crossings,
    becomes the reduced Khovanov complex of a nonempty link and has nonzero
    homology.  Thus two such summands force reduced rank at least two.  This
    remains valid before the marked endpoint has appeared: reduced base change
    at its later appearance is additive, and every completed summand still
    contains the marked edge.  The last crossing is inspected before scalar
    cancellation, which can also save the final elimination.

    An early result supplies a lower bound and replay data, NOT an exact rank
    or an independent small topological certificate.  Replaying the preceding
    scanner operations is necessary to verify that the two objects are direct
    summands.  Resource exhaustion raises ScanLimit.
    """
    pd = [tuple(row) for row in pd]
    if not pd:
        return {"status": "UNKNOT", "reduced_rank": 1, "lower_bound": 1,
                "by_degree": {0: 1}, "stats": {}, "order": [],
                "method": "pointed-khovanov-F2-decision", "certificate": None}
    pd, order, cut, endpoints, edge, scan = _prepare_scan(
        pd, order, edge, max_objects, seconds, shape_cache)
    n = len(order)
    for position, i in enumerate(order):
        last = position == n - 1
        scan.add_crossing(cut[i], reduce_now=not last)
        if check_d_squared:
            scan.check_d_squared()
        if early_stop:
            isolated = _isolated_summands(scan)
            if len(isolated) >= 2:
                return {"status": "KNOTTED", "reduced_rank": None, "lower_bound": len(isolated),
                        "stats": dict(scan.stats, **scan.algebra.stats), "order": order,
                        "marked_edge": edge, "method": "pointed-isolated-summands",
                        "certificate": {"kind": "isolated-summands-replay-data",
                                        "stage": position + 1, "remaining_crossings": n - position - 1,
                                        "before_final_elimination": last, "objects": isolated}}
        if last:
            scan.eliminate()
            scan.stats["max_objects_after_elimination"] = max(
                scan.stats["max_objects_after_elimination"], scan.live)
            if check_d_squared:
                scan.check_d_squared()
    by_degree = _terminal_rank(scan, endpoints)
    return {"status": "UNKNOT" if scan.live == 1 else "KNOTTED", "reduced_rank": scan.live,
            "lower_bound": scan.live, "by_degree": by_degree,
            "stats": dict(scan.stats, **scan.algebra.stats), "order": order, "marked_edge": edge,
            "method": "pointed-khovanov-F2-decision", "certificate": None}
