"""Optional decision scanner with first-jet queries before Schur updates.

Whole components are discarded when contractible and replaced by a matching
when primitive-interval rigidity certifies equality of every classical
completion's total rank.  This loses grading information and is deliberately
not an exact graded-homology API.  It is not the default recognition backend.
"""
from time import monotonic

from .closure_scan import complete_matching
from .diagram import Diagram
from .first_jet import FirstJetBudget, first_jet_profile
from .ordering import best_scan_order, repeated_stages, validate_order
from .scan_fast import FastScan


class _Account:
    def __init__(self, scan, limit):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError("first_jet_max_work must be a nonnegative integer or None")
        self.scan, self.limit, self.used = scan, limit, 0

    def __call__(self, amount=1):
        self.scan._check()
        if self.limit is not None and self.used + amount > self.limit:
            raise FirstJetBudget("first-jet driver observation allowance exhausted")
        self.used += amount

    def profile(self, group, audit):
        remaining = None if self.limit is None else self.limit - self.used
        try:
            data = first_jet_profile(self.scan, group, max_work=remaining, audit=audit)
        except FirstJetBudget:
            # The query returned no partial certificate.  Reserve its whole
            # remaining allowance and disable observation at the driver.
            if self.limit is not None:
                self.used = self.limit
            raise
        if data is not None:
            self.used += data['work_units']
        return data


def _groups(scan, work):
    seen = bytearray(len(scan.mid))
    for root, matching in enumerate(scan.mid):
        work()
        if matching is None or seen[root]:
            continue
        stack, group = [root], []
        seen[root] = 1
        while stack:
            work()
            vertex = stack.pop()
            group.append(vertex)
            for other in scan.out[vertex]:
                work()
                if not seen[other]:
                    seen[other] = 1
                    stack.append(other)
            for other in scan.inc[vertex]:
                work()
                if not seen[other]:
                    seen[other] = 1
                    stack.append(other)
        group.sort()
        yield group


def _install(scan, proposals, work):
    """Prepare an entire replacement state, then publish it atomically."""
    remove, representatives = set(), {}
    for data in proposals:
        work()
        group = data['vertices']
        remove.update(group)
        if data['kappa'] == 1:
            representatives[group[0]] = data['matching']
    retained = []
    for vertex, matching in enumerate(scan.mid):
        work()
        if matching is not None and (vertex not in remove or vertex in representatives):
            retained.append(vertex)
    positions = {vertex: i for i, vertex in enumerate(retained)}
    mid, degrees, outgoing, incoming = [], [], [], []
    for vertex in retained:
        work()
        mid.append(scan.mid[vertex])
        # This is an arbitrary homological shift of a rank-only replacement.
        # No later API may report these degree counts as original homology.
        degrees.append(scan.deg[vertex])
        row = {}
        if vertex not in representatives:
            for target, value in scan.out[vertex].items():
                work()
                row[positions[target]] = value
        outgoing.append(row)
        incoming.append(set())
    for source, row in enumerate(outgoing):
        work()
        for target in row:
            work()
            incoming[target].add(source)
    removed = scan.live - len(mid)
    new_cache = {}
    work()
    scan.mid, scan.deg, scan.out, scan.inc = mid, degrees, outgoing, incoming
    scan.live, scan.composed = len(mid), new_cache
    return removed


def first_jet_khovanov_decide(pd, *, order=None, max_objects=None, seconds=None,
                              shape_cache=None, first_jet_max_work=1_000_000,
                              check_d_squared=False, audit_jets=False,
                              replacements=True, closure_bounds=True):
    """Recognize a validated classical knot using a bounded optional observer.

    PD input is validated here.  Each crossing is fully allocated before the
    first-jet query, so max_objects still bounds temporary allocation.  Local
    observation exhaustion discards every uninstalled proposal from that
    stage, disables further observation, and performs ordinary cancellation
    on the intact state.  Global ScanLimit propagates from this raw API.

    ``replacements=False`` and ``closure_bounds=False`` are research ablations.
    The returned ranks are capped at three; no bigraded profile is exported.
    ``max_gap`` counts actual crossings between one-object checkpoints,
    including pre-observation allocation and the terminal segment.  The
    conditional cost bound depends on both this gap and frontier width.
    """
    deadline = None if seconds is None else monotonic() + seconds
    diagram = Diagram.from_pd(pd)
    pd = list(diagram.pd)
    if shape_cache is None:
        # Finish order selection below before applying the same repeated-stage
        # shape policy used by the existing optional scanners.
        cache_override = None
    else:
        cache_override = bool(shape_cache)
    scan = FastScan(max_objects=max_objects, deadline=deadline, shape_cache=False)
    work = _Account(scan, first_jet_max_work)
    scan._check()
    order = (best_scan_order(pd, tries=min(len(pd), 12)) if pd else []) if order is None else validate_order(len(pd), order)
    scan._check()
    cache = (len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
             if cache_override is None else cache_override)
    # No tangle state has been constructed yet, so replacing its empty algebra
    # with the requested cache configuration preserves the initial object.
    if cache:
        scan = FastScan(max_objects=max_objects, deadline=deadline, shape_cache=True)
        work.scan = scan
    stats = dict(queries=0, eligible=0, replacements=0, contractible_discards=0,
                 scalar_pairs_avoided=0, objects_removed=0, exhausted=False,
                 checkpoint_count=0, max_gap=0, scanned=0, work_units=0)
    events = []
    last_checkpoint = 0

    def result(status, method, capped):
        stats['work_units'] = work.used
        return dict(status=status, method=method, rank_capped=capped, rank_cap=3,
                    order=order, events=events, first_jet_stats=dict(stats),
                    stats=dict(scan.stats, **scan.algebra.stats),
                    profile_contract='total-rank decision only; original grading not retained')

    for stage, index in enumerate(order, 1):
        scan.add_crossing(pd[index], reduce_now=False)
        stats['scanned'] = stage
        stats['max_gap'] = max(stats['max_gap'], stage - last_checkpoint)
        if check_d_squared:
            scan.check_d_squared()
        if stage < len(order) and not stats['exhausted']:
            proposals, observations = [], []
            lower, completions = 0, {}
            try:
                for group in _groups(scan, work):
                    # Discovery knows types before doing polynomial or rank
                    # work; this also avoids spending an unreported query
                    # allowance on a declined mixed component.
                    matching = scan.mid[group[0]]
                    if any(scan.mid[v] != matching for v in group):
                        continue
                    stats['queries'] += 1
                    data = work.profile(group, audit_jets)
                    if data is None:
                        continue
                    stats['eligible'] += 1
                    bound = 2 if data['kappa'] == 1 else 0
                    if data['kappa'] > 0 and closure_bounds:
                        if matching not in completions:
                            suffix = [pd[j] for j in order[stage:]]
                            completions[matching] = complete_matching(
                                suffix, scan.algebra.pairs[matching], work)
                        _, count = completions[matching]
                        data['completion_components'] = count
                        if count == 1:
                            bound = 2 * data['kappa']
                        elif data['kappa'] == 1:
                            bound = 4
                    data['rank_lower_bound'] = bound
                    observations.append(data)
                    lower += bound
                    if lower >= 4:
                        events.append(dict(type='first-jet-obstruction', stage=stage,
                                           blocks=observations, rank_lower_bound_capped=3))
                        return result('KNOTTED', 'first-jet-bound', 3)
                    if replacements and data['kappa'] <= 1:
                        proposals.append(data)
                if proposals:
                    removed = _install(scan, proposals, work)
                    stats['objects_removed'] += removed
                    stats['replacements'] += sum(x['kappa'] == 1 for x in proposals)
                    stats['contractible_discards'] += sum(x['kappa'] == 0 for x in proposals)
                    stats['scalar_pairs_avoided'] += sum(x['scalar_rank'] for x in proposals)
                    events.append(dict(type='first-jet-replacement', stage=stage,
                                       blocks=proposals, objects_removed=removed))
            except FirstJetBudget:
                stats['exhausted'] = True
        scan.eliminate()
        scan.stats['max_objects_after_elimination'] = max(
            scan.stats['max_objects_after_elimination'], scan.live)
        if check_d_squared:
            scan.check_d_squared()
        if scan.live == 1:
            stats['checkpoint_count'] += 1
            last_checkpoint = stage
    scan._check()
    rank = scan.total_rank() if pd else 2
    if rank < 2 or rank % 2:
        raise ArithmeticError('a validated knot has invalid unreduced characteristic-two rank')
    return result('UNKNOT' if rank == 2 else 'KNOTTED', 'closed-rank', min(3, rank))
