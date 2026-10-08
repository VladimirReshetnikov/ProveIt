"""Exact direct-sum sharing for the ungraded fastunknot F2 scanning category.

This is an opt-in research backend.  It retains one explicitly serialized
representative of each *observed* differential-graph component, up to a uniform
homological shift.  Matching labels and every morphism coefficient are included
in the key.  No graph-isomorphism oracle or hash-only identification is used.

Repeated summands are weighted by polynomials in Z[z], never by F2 scalars.
The standard scanner is imported and remains unchanged.  Add this directory to
PYTHONPATH alongside the repository's fast/ directory to use the extension.
"""
from __future__ import annotations

from collections import defaultdict
from time import monotonic

from fastunknot.scan_fast import FastScan
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order, repeated_stages, validate_order


def components(scan):
    """Connected components of the undirected nonzero-differential graph.

    Object order is inherited, then compacted.  Equal resulting serialization
    gives an explicit chain isomorphism.  Unequal keys can still be isomorphic;
    the algorithm simply forgoes that possible saving.
    """
    seen = bytearray(len(scan.mid))
    for root, matching in enumerate(scan.mid):
        if matching is None or seen[root]:
            continue
        seen[root] = 1
        stack = [root]
        group = []
        while stack:
            v = stack.pop()
            group.append(v)
            for w in scan.out[v]:
                if not seen[w]:
                    seen[w] = 1
                    stack.append(w)
            for w in scan.inc[v]:
                if not seen[w]:
                    seen[w] = 1
                    stack.append(w)
        group.sort()
        yield group


def component_key(scan, group):
    """Return the exact serialized component and its uniform degree shift."""
    local = {v: i for i, v in enumerate(group)}
    shift = min(scan.deg[v] for v in group)
    key = tuple(
        (scan.mid[v], scan.deg[v] - shift,
         tuple(sorted((local[w], value) for w, value in scan.out[v].items())))
        for v in group
    )
    return key, shift


class ComponentScan(FastScan):
    """FastScan with multiplicity polynomials attached to component types."""

    def __init__(self, *args, rank_cap=None, **kwargs):
        super().__init__(*args, **kwargs)
        if rank_cap is not None and (type(rank_cap) is not int or rank_cap < 1):
            raise ValueError("rank_cap must be a positive integer or None")
        self.rank_cap = rank_cap
        self.weights = [{0: 1}]
        self.owner = [0]
        self.stage_history = []
        self.stats.update(
            component_merges=0,
            max_component_objects=0,
            max_representative_objects=1,
            max_representative_components=1,
            multiplicity_updates=0,
        )
        expanded_stat = ("max_expanded_after_elimination" if rank_cap is None else
                         "max_expanded_after_elimination_lower_bound")
        self.stats[expanded_stat] = 1

    def add_crossing(self, slots, reduce_now=True):
        if not reduce_now:
            raise ValueError("ComponentScan requires elimination after every crossing")
        old_mid, old_owner = self.mid, self.owner
        super().add_crossing(slots, reduce_now=True)
        # FastScan creates this contiguous block for each old live object.
        # Its algebra still holds exactly this crossing's gluing cache.
        ancestry = []
        for v, matching in enumerate(old_mid):
            if matching is not None:
                closed0 = self.algebra.glue(matching, 0)[1]
                closed1 = self.algebra.glue(matching, 1)[1]
                count = (1 << closed0) + (1 << closed1)
                ancestry.extend([old_owner[v]] * count)
        if len(ancestry) != len(self.mid):
            raise ArithmeticError("crossing ancestry did not match the scanner allocation")
        self._compress(ancestry)

    def _compress(self, ancestry):
        # Dictionary equality verifies the complete key even on hash collision.
        types = {}
        encountered = largest = expanded = 0
        weight_totals = [sum(weight.values()) for weight in self.weights]
        for group in components(self):
            self._check()
            encountered += 1
            largest = max(largest, len(group))
            parent = ancestry[group[0]]
            if any(ancestry[v] != parent for v in group):
                raise ArithmeticError("a differential joined independent parent summands")
            expanded += len(group) * weight_totals[parent]
            key, shift = component_key(self, group)
            weight = types.setdefault(key, defaultdict(int))
            if self.rank_cap is None:
                for h, count in self.weights[parent].items():
                    weight[h + shift] += count
                    self.stats["multiplicity_updates"] += 1
            else:
                # Evaluation z=1 followed by saturation is a semiring map.
                # It may only be used for final rank decisions, not gradings.
                weight[0] = min(self.rank_cap, weight[0] + weight_totals[parent])
                self.stats["multiplicity_updates"] += 1

        mid, deg, out, inc, owners, weights = [], [], [], [], [], []
        for index, (key, weight) in enumerate(types.items()):
            offset = len(mid)
            for matching, degree, row in key:
                mid.append(matching)
                deg.append(degree)
                out.append({offset + w: value for w, value in row})
                inc.append(set())
                owners.append(index)
            weights.append(dict(weight))
        for source, row in enumerate(out):
            for target in row:
                inc[target].add(source)
        self.mid, self.deg, self.out, self.inc = mid, deg, out, inc
        self.owner, self.weights, self.live = owners, weights, len(mid)
        stats = self.stats
        stats["component_merges"] += encountered - len(types)
        stats["max_component_objects"] = max(stats["max_component_objects"], largest)
        stats["max_representative_objects"] = max(stats["max_representative_objects"], len(mid))
        stats["max_representative_components"] = max(stats["max_representative_components"], len(types))
        expanded_stat = ("max_expanded_after_elimination" if self.rank_cap is None else
                         "max_expanded_after_elimination_lower_bound")
        stats[expanded_stat] = max(stats[expanded_stat], expanded)
        self.stage_history.append(dict(
            stage=len(self.stage_history) + 1,
            encountered_components=encountered,
            representative_components=len(types),
            representative_objects=len(mid),
            expanded_objects=expanded,
            largest_component=largest,
            expanded_objects_is_lower_bound=self.rank_cap is not None,
        ))

    def total_rank(self):
        if self.points:
            raise ValueError("the diagram is not closed yet")
        if any(self.out):
            raise ArithmeticError("minimal closed complex has a nonzero differential")
        rank = sum(sum(self.weights[self.owner[v]].values())
                   for v, matching in enumerate(self.mid) if matching is not None)
        return rank if self.rank_cap is None else min(self.rank_cap, rank)

    def ranks_by_degree(self):
        if self.rank_cap is not None:
            raise ValueError("absolute gradings were discarded by saturated multiplicities")
        ranks = defaultdict(int)
        for v, matching in enumerate(self.mid):
            if matching is not None:
                for shift, count in self.weights[self.owner[v]].items():
                    ranks[self.deg[v] + shift] += count
        return dict(sorted(ranks.items()))


def compressed_khovanov_rank(pd, *, order=None, max_objects=None, seconds=None,
                             check_d_squared=False, shape_cache=None):
    """Same rank and raw homological grading as fastunknot.khovanov_rank.

    ``pd`` must already have been validated as a knot diagram, as for the
    baseline scanner.  The optional object ceiling concerns physically stored
    representatives, not the potentially exponential virtual multiplicity.
    """
    pd = [tuple(crossing) for crossing in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        return dict(rank=2, reduced_rank=1, by_degree={0: 2}, stats={}, order=[],
                    backend="component-sharing", stages=[])
    deadline = None if seconds is None else monotonic() + seconds
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12))
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan = ComponentScan(max_objects=max_objects, deadline=deadline, shape_cache=shape_cache)
    for i in order:
        scan.add_crossing(pd[i])
        if check_d_squared:
            scan.check_d_squared()
    rank = scan.total_rank()
    if rank % 2:
        raise ArithmeticError("odd unreduced F2 rank for a knot")
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(rank=rank, reduced_rank=rank // 2, by_degree=scan.ranks_by_degree(),
                stats=stats, order=order, backend="component-sharing", stages=scan.stage_history)


def compressed_khovanov_decide(pd, *, order=None, max_objects=None, seconds=None,
                               check_d_squared=False, shape_cache=None):
    """Exact unknot verdict with multiplicities in the saturated semiring S_3.

    The diagram MUST be validated as one component before calling.  The result
    gives min(3, unreduced rank), not an exact rank when this value is three.
    No verdict is taken from a partial scan or a large virtual object count.
    """
    pd = [tuple(crossing) for crossing in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        return dict(status="UNKNOT", rank_capped=2, rank_cap=3, stats={}, order=[],
                    backend="component-sharing-saturated", stages=[])
    deadline = None if seconds is None else monotonic() + seconds
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12))
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan = ComponentScan(max_objects=max_objects, deadline=deadline,
                         shape_cache=shape_cache, rank_cap=3)
    for i in order:
        scan.add_crossing(pd[i])
        if check_d_squared:
            scan.check_d_squared()
    capped = scan.total_rank()
    if capped not in (2, 3):
        raise ArithmeticError("a validated knot must have unreduced rank at least two")
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(status="UNKNOT" if capped == 2 else "KNOTTED", rank_capped=capped,
                rank_cap=3, stats=stats, order=order, backend="component-sharing-saturated",
                stages=scan.stage_history)

