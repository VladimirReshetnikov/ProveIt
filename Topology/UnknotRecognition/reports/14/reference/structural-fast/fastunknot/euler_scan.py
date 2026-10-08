"""Optional exact suffix-Euler certificates for component-sharing scans.

The bounded Euler state computation may fail inconclusively; the exact capped
scanner then continues.  Euler coefficients are signed integers and are NEVER
saturated.  Only the final nonnegative homology-rank lower bound is capped.
"""
from __future__ import annotations

from time import monotonic

from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order, repeated_stages, validate_order
from fastunknot.planar import Planar

if __package__:
    from .component_scan import ComponentScan
else:
    from component_scan import ComponentScan


class EulerBudget(Exception):
    """A rejected Euler inference; this exception is not a knot verdict."""


class SuffixEuler:
    """Memoized exact Euler functional on suffixes of a fixed scan order.

    State keys contain a suffix index and the complete matching pairs.  For a
    crossing that creates c_s closed circles in smoothing s, the recurrence is

        E_i(m) = 2**c_0 E_{i+1}(m_0) - 2**c_1 E_{i+1}(m_1).

    Terminal E_n(empty)=1.  An iterative dependency stack avoids Python's
    recursion limit on long diagrams.  At most max_states states are registered
    over the lifetime of the object; budget exhaustion leaves all existing
    exact values valid but the caller should stop using the optional inference.
    """

    def __init__(self, pd, order, *, max_states=4096, deadline=None):
        if max_states is not None and (type(max_states) is not int or max_states < 0):
            raise ValueError("Euler max_states must be a nonnegative integer or None")
        self.max_states = max_states
        self.deadline = deadline
        self.algebras = []
        points = frozenset()
        for index in order:
            algebra = Planar(shape_cache=False)
            algebra.stage(points, pd[index])
            self.algebras.append(algebra)
            points = algebra.new_points()
        if points:
            raise ValueError("the suffix must end with empty boundary")
        self.cache = {}
        self.pending = {}
        self.stats = dict(states=0, evaluations=0, max_coefficient_bits=0)

    def _check(self):
        if self.deadline is not None and monotonic() > self.deadline:
            raise ScanLimit("time budget exhausted in suffix Euler computation")

    def evaluate(self, stage, pairs):
        if not 0 <= stage <= len(self.algebras):
            raise ValueError("invalid suffix stage")
        self.stats["evaluations"] += 1
        root = (stage, tuple(pairs))
        stack = [root]
        while stack:
            self._check()
            key = stack[-1]
            if key in self.cache:
                stack.pop()
                continue
            i, matching = key
            if key not in self.pending:
                if self.max_states is not None and self.stats["states"] >= self.max_states:
                    raise EulerBudget("suffix Euler state budget exhausted")
                self.stats["states"] += 1
                if i == len(self.algebras):
                    if matching:
                        raise ArithmeticError("a terminal Euler matching is nonempty")
                    self.cache[key] = 1
                    self.stats["max_coefficient_bits"] = max(1, self.stats["max_coefficient_bits"])
                    stack.pop()
                    continue
                algebra = self.algebras[i]
                m = algebra.intern(matching)
                m0, c0, _ = algebra.glue(m, 0)
                m1, c1, _ = algebra.glue(m, 1)
                child0 = (i + 1, algebra.pairs[m0])
                child1 = (i + 1, algebra.pairs[m1])
                self.pending[key] = (child0, c0, child1, c1)
            child0, c0, child1, c1 = self.pending[key]
            if child0 not in self.cache:
                stack.append(child0)
                continue
            if child1 not in self.cache:
                stack.append(child1)
                continue
            value = (self.cache[child0] << c0) - (self.cache[child1] << c1)
            self.cache[key] = value
            self.stats["max_coefficient_bits"] = max(
                self.stats["max_coefficient_bits"], abs(value).bit_length())
            del self.pending[key]
            stack.pop()
        return self.cache[root]


def component_euler_bound(scan, engine, stage, *, cap=None):
    """Return the sum of absolute Euler characteristics of completed summands.

    If the scan has capped weights, cap must be at most that weight cap.  The
    returned Euler values themselves remain exact signed integers.
    """
    if scan.rank_cap is not None and (cap is None or cap > scan.rank_cap):
        raise ValueError("the requested bound exceeds available saturated multiplicities")
    values = {}
    for matching in set(scan.mid):
        if matching is not None:
            values[matching] = engine.evaluate(stage, scan.algebra.pairs[matching])
    chi = [0] * len(scan.weights)
    for v, matching in enumerate(scan.mid):
        if matching is not None:
            value = values[matching]
            chi[scan.owner[v]] += -value if scan.deg[v] % 2 else value
    bound = sum(sum(weight.values()) * abs(value)
                for weight, value in zip(scan.weights, chi))
    if cap is not None:
        bound = min(cap, bound)
    return bound, chi


def euler_compressed_khovanov_decide(pd, *, order=None, max_objects=None, seconds=None,
                                    check_d_squared=False, shape_cache=None,
                                    euler_max_states=4096):
    """Exact decision, with optional early componentwise Euler lower bounds.

    The input must already be validated as a classical one-component knot
    diagram.  Euler-state exhaustion merely disables the optional certificate;
    ordinary capped scanning continues.  Object/time exhaustion raises ScanLimit.
    """
    pd = [tuple(crossing) for crossing in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        return dict(status="UNKNOT", method="closed-rank", rank_capped=2, rank_cap=3,
                    stage=0, crossings=0, stats={}, order=[], euler_stats={}, euler_exhausted=False)
    deadline = None if seconds is None else monotonic() + seconds
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12))
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    engine = SuffixEuler(pd, order, max_states=euler_max_states, deadline=deadline)
    scan = ComponentScan(max_objects=max_objects, deadline=deadline,
                         shape_cache=shape_cache, rank_cap=3)
    exhausted = False
    for stage, index in enumerate(order, 1):
        scan.add_crossing(pd[index])
        if check_d_squared:
            scan.check_d_squared()
        # One copy of one component has the whole knot's Euler magnitude, two.
        # No inference work can help until an actual direct-sum split appears.
        copies = sum(sum(weight.values()) for weight in scan.weights)
        if not exhausted and stage < len(order) and copies > 1:
            try:
                bound, chi = component_euler_bound(scan, engine, stage, cap=3)
            except EulerBudget:
                exhausted = True
            else:
                if bound >= 3:
                    stats = dict(scan.stats)
                    stats.update(scan.algebra.stats)
                    return dict(status="KNOTTED", method="component-euler", rank_cap=3,
                                rank_lower_bound_capped=bound, stage=stage, crossings=len(order),
                                euler_characteristics=chi,
                                multiplicities_capped=[sum(w.values()) for w in scan.weights],
                                stats=stats, order=order, euler_stats=dict(engine.stats),
                                euler_exhausted=exhausted)
    capped = scan.total_rank()
    if capped not in (2, 3):
        raise ArithmeticError("a validated knot must have unreduced rank at least two")
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(status="UNKNOT" if capped == 2 else "KNOTTED", method="closed-rank",
                rank_capped=capped, rank_cap=3, stage=len(order), crossings=len(order),
                stats=stats, order=order, euler_stats=dict(engine.stats), euler_exhausted=exhausted)
