"""Decision-only classical closure bounds and single-survivor resets.

Report 28's first-jet rule applies to whole radical single-matching summands
with an actual knot completion. Pure blocks also have closure-uniform bounds.
Resets preserve total rank, not isotopy or bigraded homology. Local observation
exhaustion resumes the same capped scan; global limits remain ScanLimit.
"""
from collections import Counter
from time import monotonic

from .component_scan import ComponentScan, components
from .diagram import DisjointSet
from .geometry import ScanLimit
from .ordering import best_scan_order, repeated_stages, validate_order


class ClosureBudget(Exception):
    """Optional observation stopped without changing the scan."""


class Work:
    def __init__(self, limit, deadline):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError("closure_max_work must be a nonnegative integer or None")
        self.limit, self.deadline, self.used = limit, deadline, 0

    def __call__(self, amount=1):
        if self.deadline is not None and monotonic() >= self.deadline:
            raise ScanLimit("time budget exhausted in closure observation")
        if self.limit is not None and self.used + amount > self.limit:
            raise ClosureBudget("closure observation allowance exhausted")
        self.used += amount


def _rank(columns, check):
    pivots = {}
    for column in columns:
        check()
        while column:
            check()
            bit = column.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = column
                break
            column ^= pivots[bit]
    return len(pivots)


def _linear_parity(value, check):
    parity = 0
    while value:
        check()
        low = value & -value
        monomial = low.bit_length() - 1
        parity ^= int(monomial != 0 and monomial & (monomial - 1) == 0)
        value ^= low
    return parity


def certify_block(scan, group, check=lambda: None):
    """Read a whole radical block; genuine chain-complex provenance is required.

    Returns None for mixed matchings or scalar units. It verifies attachments,
    degrees and polynomial domains, but cannot establish geometric provenance
    or d squared from an arbitrary caller-supplied matrix.
    """
    group = tuple(group)
    members = set(group)
    if not group or len(members) != len(group):
        raise ValueError("invalid closure block vertices")
    for v in group:
        check()
        if type(v) is not int or not 0 <= v < len(scan.mid) or scan.mid[v] is None:
            raise ValueError("invalid live closure block vertex")
        if any(w not in members for w in scan.out[v]) or any(w not in members for w in scan.inc[v]):
            raise ValueError("closure block has external differential attachments")
    matching = scan.mid[group[0]]
    if any(scan.mid[v] != matching for v in group):
        return None
    variables = len(scan.algebra.pairs[matching])
    if not variables:
        return None
    layers = {}
    for v in group:
        layers.setdefault(scan.deg[v], []).append(v)
    positions = {v: j for layer in layers.values() for j, v in enumerate(layer)}
    columns = {}
    theta, pure = None, True
    parity_cache = {}
    for v in group:
        check()
        column = 0
        for w, value in scan.out[v].items():
            check()
            if type(value) is not int or value <= 0 or value.bit_length() > 1 << variables:
                raise ValueError("invalid closure dot polynomial")
            if scan.deg[w] != scan.deg[v] + 1:
                raise ValueError("closure differential has invalid degree")
            if value & 1:
                return None
            if theta is None:
                theta = value
            pure &= theta == value
            if value not in parity_cache:
                parity_cache[value] = _linear_parity(value, check)
            if parity_cache[value]:
                column |= 1 << positions[w]
        columns.setdefault(scan.deg[v], []).append(column)
    kappa = len(group) - sum(_rank(row, check) for row in columns.values())
    if kappa < 1:
        raise ArithmeticError("bounded radical block has no first-jet survivor")
    # An even pure block with an edge has rank >=4 under every classical
    # closure. An odd pure block has multiplier kappa for every such closure.
    even_edge = pure and theta is not None and not parity_cache[theta]
    lower = 4 if even_edge else 2 * kappa if pure else 0
    return dict(vertices=list(group), matching=matching, kappa=kappa,
                pure=pure, theta=theta, has_edge=theta is not None,
                closure_uniform_lower_bound=lower)


def complete_matching(suffix, pairs, check=lambda: None):
    """Splice a geometric frontier matching and verify the resulting link PD.

    Returns (canonical PD, number of link components). Nonempty suffix only;
    removed smoothing circles were already accounted for by the exact scan.
    Sphericity is checked, but it does not replace relative-summand provenance.
    """
    suffix = [tuple(row) for row in suffix]
    if not suffix or any(len(row) != 4 for row in suffix):
        raise ValueError("closure requires a nonempty suffix of crossings")
    counts = Counter()
    for row in suffix:
        check()
        counts.update(row)
    pairs = tuple(tuple(pair) for pair in pairs)
    if any(len(pair) != 2 or pair[0] == pair[1] for pair in pairs):
        raise ValueError("invalid closure matching arc")
    ends = [x for pair in pairs for x in pair]
    if (len(ends) != len(set(ends)) or set(ends) != {x for x, n in counts.items() if n == 1}
            or any(n not in (1, 2) for n in counts.values())):
        raise ValueError("matching must cover exactly the suffix frontier")
    ids = {x: i for i, x in enumerate(sorted(counts))}
    ds = DisjointSet(len(ids))
    for a, b in pairs:
        check()
        ds.union(ids[a], ids[b])
    relabel = {}
    pd = []
    for row in suffix:
        check()
        roots = [ds.find(ids[x]) for x in row]
        pd.append(tuple(relabel.setdefault(x, len(relabel)) for x in roots))
    n = len(pd)
    where = {}
    alpha = [-1] * (4 * n)
    strands, shadow = DisjointSet(4 * n), DisjointSet(n)
    for i, row in enumerate(pd):
        check()
        strands.union(4 * i, 4 * i + 2)
        strands.union(4 * i + 1, 4 * i + 3)
        for j, x in enumerate(row):
            dart = 4 * i + j
            if x in where:
                other = where.pop(x)
                alpha[dart], alpha[other] = other, dart
                strands.union(dart, other)
                shadow.union(i, other // 4)
            else:
                where[x] = dart
    if where or -1 in alpha:
        raise ValueError("completed edges must occur twice")
    seen, faces = set(), 0
    for start in range(4 * n):
        if start in seen:
            continue
        faces += 1
        dart = start
        while dart not in seen:
            check()
            seen.add(dart)
            a = alpha[dart]
            dart = (a & -4) | ((a + 1) & 3)
    if faces != n + 2 * len({shadow.find(i) for i in range(n)}):
        raise ValueError("matching completion is not classical")
    return pd, len({strands.find(i) for i in range(4 * n)})


def closure_khovanov_decide(pd, *, order=None, max_objects=None, seconds=None,
                            check_d_squared=False, closure_max_work=1_000_000,
                            reset=True, shape_cache=None):
    """Capped exact recognition with optional rank-preserving diagram resets.

    The input must be a validated classical knot. The selected crossing order
    is retained across resets. This API deliberately exposes no graded ranks.
    """
    pd = [tuple(row) for row in pd]
    deadline = None if seconds is None else monotonic() + seconds
    work = Work(closure_max_work, deadline)
    order = (best_scan_order(pd, tries=min(len(pd), 12)) if pd else []) if order is None else validate_order(len(pd), order)
    current = [pd[i] for i in order]
    exhausted, events, scans = False, [], []
    scanned = max_gap = nonsingleton = 0
    while True:
        cache = shape_cache
        if cache is None:
            cache = len(current) >= 16 and 8 * repeated_stages(current, range(len(current))) >= len(current)
        scan = ComponentScan(max_objects=max_objects, deadline=deadline, rank_cap=3,
                             shape_cache=cache)
        scan._check()
        restarted = False
        for stage, crossing in enumerate(current, 1):
            scan._check()
            scan.add_crossing(crossing)
            scanned += 1
            max_gap = max(max_gap, stage)
            if check_d_squared:
                scan.check_d_squared()
            if stage == len(current) or exhausted:
                continue
            try:
                work(len(scan.mid))
                groups = list(components(scan))
                records, lower, candidate = [], 0, None
                completions = {}
                for group in groups:
                    data = certify_block(scan, group, work)
                    if data is None:
                        continue
                    nonsingleton += int(data['has_edge'])
                    owner = scan.owner[group[0]]
                    if any(scan.owner[v] != owner for v in group):
                        raise ArithmeticError("closure block mixes independent owners")
                    copies = sum(scan.weights[owner].values())
                    bound = data['closure_uniform_lower_bound']
                    residual = None
                    if bound * copies < 4:
                        m = data['matching']
                        if m not in completions:
                            completions[m] = complete_matching(current[stage:], scan.algebra.pairs[m], work)
                        residual, count = completions[m]
                        data['completion_components'] = count
                        if count == 1:
                            bound = max(bound, 2 * data['kappa'])
                            if len(groups) == copies == data['kappa'] == 1:
                                candidate = residual
                        elif data['pure']:
                            # Each pure quiver interval contributes at least
                            # the nonempty link rank, hence at least four.
                            bound = max(bound, 4)
                    data.update(multiplicity=copies, lower_bound=bound * copies)
                    records.append(data)
                    lower += bound * copies
                    if lower >= 4:
                        events.append(dict(type='closure-obstruction', stage=stage, blocks=records,
                                           rank_lower_bound_capped=3))
                        break
            except ClosureBudget:
                exhausted = True
                continue
            if lower >= 4:
                scans.append(dict(scan.stats, **scan.algebra.stats))
                return _result('KNOTTED', 'closure-bound', 3, order, events, scans,
                               scanned, max_gap, nonsingleton, work, exhausted)
            if reset and candidate is not None:
                events.append(dict(type='reset', stage=stage, blocks=records, residual=candidate))
                scans.append(dict(scan.stats, **scan.algebra.stats))
                current, restarted = candidate, True
                break
        if restarted:
            continue
        scan._check()
        rank = scan.total_rank() if current else 2
        if rank not in (2, 3):
            raise ArithmeticError("validated knot has invalid capped rank")
        scans.append(dict(scan.stats, **scan.algebra.stats))
        return _result('UNKNOT' if rank == 2 else 'KNOTTED', 'closed-rank', rank,
                       order, events, scans, scanned, max_gap, nonsingleton, work, exhausted)


def _result(status, method, rank, order, events, scans, scanned, gap, blocks, work, exhausted):
    return dict(status=status, method=method, rank_capped=rank, rank_cap=3,
                order=order, events=events, segment_stats=scans,
                closure_stats=dict(scanned=scanned, max_gap=gap,
                                   resets=sum(e['type'] == 'reset' for e in events),
                                   nonsingleton_observations=blocks, work_units=work.used,
                                   exhausted=exhausted))
