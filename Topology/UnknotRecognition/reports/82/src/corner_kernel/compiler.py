"""First-return matching from unweighted orbit-count callbacks.

Subset coning is already present in ProveIt's sparse-incidence machinery.
Here it is specialized to degree-two boundary components, and supplemented
with the zero-gap information essential for marked surface gluing.
SPDX-License-Identifier: MIT-0.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from typing import Callable, Sequence
from .surfaces import Surface, Edge, make_kernel, Kernel

Extra = tuple[tuple[int, int], ...]
Count = Callable[[Extra], int]


class Incomplete(RuntimeError):
    """A work budget or underlying orbit calculation did not finish."""


@dataclass(frozen=True)
class Port:
    label: str
    surface: int
    start: int
    end: int
    induced_reverse: int = 0

    def __post_init__(self):
        if not isinstance(self.label, str) or not self.label:
            raise ValueError('port label must be nonempty')
        for x in (self.surface, self.start, self.end):
            if type(x) is not int or x < 0:
                raise ValueError('port indices must be nonnegative integers')
        if type(self.induced_reverse) is not int or self.induced_reverse not in (0, 1):
            raise ValueError('induced_reverse must be zero or one')


@dataclass(frozen=True)
class Matching:
    mate: tuple[int, ...]
    positive: tuple[bool, ...]
    passive_boundary: int
    queries: int
    maximum_extra_pairings: int
    transcript: tuple[dict, ...]


def _star(points: Sequence[int]) -> Extra:
    if not points:
        return ()
    hub = points[0]
    return tuple((hub, z) for z in dict.fromkeys(points[1:]) if z != hub)


def recover_matching(points: Sequence[int], vertex_count: Count,
                     residual_count: Count, *, max_queries: int | None = None,
                     check: Callable[[], None] | None = None) -> Matching:
    """Recover paths in boundary minus the interiors of p marked edges.

    `vertex_count` fixes only the quotient-vertex relation V.
    `residual_count` fixes V plus all UNMARKED boundary-edge identifications R.
    Each callback takes additional singleton identifications on the SAME
    boundary-vertex occurrence universe and returns its total orbit count.
    Geometry validity (in particular degree two) is an input obligation.
    Endpoint occurrences may repeat the same integer point.
    """
    points = tuple(points)
    if len(points) % 2 or any(type(x) is not int or x < 0 for x in points):
        raise ValueError('an even list of nonnegative endpoint indices is required')
    if max_queries is not None and (type(max_queries) is not int or max_queries < 0):
        raise ValueError('invalid query budget')
    poll = check or (lambda: None)
    transcript: list[dict] = []
    max_extra = 0
    def query(kind: str, extra: Extra = ()) -> int:
        nonlocal max_extra
        poll()
        if max_queries is not None and len(transcript) >= max_queries:
            raise Incomplete('shared orbit-query budget exhausted')
        value = (vertex_count if kind == 'V' else residual_count)(extra)
        if type(value) is not int or value < 0:
            raise ValueError('count callback must return a nonnegative integer')
        transcript.append({'relation': kind, 'extra': extra, 'count': value})
        max_extra = max(max_extra, len(extra))
        return value
    cv, cr = query('V'), query('R')
    p = len(points) // 2
    if not points:
        return Matching((), (), cr, len(transcript), max_extra, tuple(transcript))
    # Detect non-degree-two terminal signatures without enumerating components.
    touched = cr - query('R', _star(points)) + 1
    if touched != p:
        raise ValueError('residual terminal classes do not have the required count')
    def contains(point: int, candidates: Sequence[int]) -> bool:
        values = tuple(points[i] for i in candidates)
        if point in values:
            return True
        star = _star(values)
        before = query('R', star)
        after = query('R', star + ((values[0], point),))
        if before - after not in (0, 1):
            raise ValueError('inconsistent orbit-count callback')
        return before == after
    remaining = list(range(len(points)))
    mate = [-1] * len(points)
    positive = [False] * len(points)
    while remaining:
        poll()
        x = remaining[0]
        candidates = remaining[1:]
        if not candidates:
            raise ValueError('unmatched endpoint')
        while len(candidates) > 1:
            cut = (len(candidates) + 1) // 2
            left = candidates[:cut]
            candidates = left if contains(points[x], left) else candidates[cut:]
        y = candidates[0]
        extra = () if points[x] == points[y] else ((points[x], points[y]),)
        if extra and query('R', extra) != cr:
            raise ValueError('alleged residual pair is disconnected')
        zero = (not extra or query('V', extra) == cv)
        mate[x] = y
        mate[y] = x
        positive[x] = positive[y] = not zero
        remaining = [i for i in remaining if i not in (x, y)]
    if cr < p:
        raise ValueError('negative passive component count')
    poll()
    return Matching(tuple(mate), tuple(positive), cr-p, len(transcript),
                    max_extra, tuple(transcript))


def compile_boundary(surfaces: Sequence[Surface], ports: Sequence[Port],
                     vertex_count: Count, residual_count: Count, *,
                     full_boundary_count: Count | None = None, **options
                     ) -> tuple[Kernel, Matching]:
    """Compile the exact boundary topology (not lengths of suppressed paths).

    Supplied Surface statistics and coherent port orientation bits must already
    be certified from the source. A unit gap in the result denotes a positive
    source path, NOT a claim that the source path had physical length one.
    """
    surfaces, ports = tuple(surfaces), tuple(ports)
    if len({p.label for p in ports}) != len(ports):
        raise ValueError('duplicate port label')
    if any(p.surface >= len(surfaces) for p in ports):
        raise ValueError('unknown owner')
    points = tuple(x for port in ports for x in (port.start, port.end))
    matching = recover_matching(points, vertex_count, residual_count, **options)
    remaining = set(range(len(ports)))
    cycles = []
    while remaining:
        first = min(remaining, key=lambda i: ports[i].label)
        owner = ports[first].surface
        start = 2*first + ports[first].induced_reverse
        endpoint = start
        edges = []
        while True:
            i, direction = divmod(endpoint, 2)
            if i not in remaining:
                raise ValueError('first-return system repeats a port')
            port = ports[i]
            if port.surface != owner:
                raise ValueError('a boundary cycle crosses source components')
            if surfaces[owner].orientable and direction != port.induced_reverse:
                raise ValueError('inconsistent supplied induced orientations')
            remaining.remove(i)
            edges.append(Edge(port.label, direction))
            exit_endpoint = endpoint ^ 1
            if matching.positive[exit_endpoint]:
                edges.append(Edge(length=1))
            endpoint = matching.mate[exit_endpoint]
            if endpoint == start:
                break
        cycles.append((owner, edges))
    kernel = make_kernel(surfaces, cycles)
    if full_boundary_count is not None:
        # In the all-corner namespace, interior quotient vertices are silent
        # orbits. A third count cancels them without extracting a new namespace.
        cap = options.get('max_queries')
        if cap is not None and matching.queries >= cap:
            raise Incomplete('shared orbit-query budget exhausted')
        poll = options.get('check') or (lambda: None)
        poll()
        total = full_boundary_count(())
        if type(total) is not int or total < 0:
            raise ValueError('invalid full-boundary orbit count')
        silent = total - sum(s.boundary for s in surfaces)
        if silent < 0:
            raise ValueError('negative silent-orbit count')
        matching = replace(matching, passive_boundary=matching.passive_boundary-silent,
                           queries=matching.queries+1,
                           transcript=matching.transcript+({'relation':'F','extra':(),
                                                            'count':total},))
    if sum(kernel.passive) != matching.passive_boundary:
        raise ValueError('source boundary counts disagree with residual orbit counts')
    return kernel, matching


def verify_count_transcript(transcript: Sequence[dict], vertex_count: Count,
                            residual_count: Count, full_boundary_count: Count | None = None) -> bool:
    """Reference recomputation checker; not a producer-independent AHT verifier.

    For upstream proof-only replay, verify every attached AHT certificate instead.
    """
    try:
        for row in transcript:
            if row['relation'] not in ('V', 'R', 'F'):
                return False
            oracle = {'V': vertex_count, 'R': residual_count, 'F': full_boundary_count}[row['relation']]
            if oracle is None:
                return False
            extra = tuple(tuple(pair) for pair in row['extra'])
            if oracle(extra) != row['count']:
                return False
        return True
    except (KeyError, TypeError, ValueError):
        return False
