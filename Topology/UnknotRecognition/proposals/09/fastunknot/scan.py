"""Khovanov homology over F2 by scanning (Bar-Natan's local algorithm).

The diagram is processed one crossing at a time.  After each step the partial
complex lives in the F2-linear dotted-cobordism category of the processed
region: objects are perfect matchings of the boundary edges (closed circles are
"delooped" into two objects), and a morphism between matchings a and b is an
F2-combination of dot-subsets of the circles of a u b~.  Composition is the
two-dimensional TQFT of the glued surface for the Frobenius algebra
F2[x]/(x^2): a component of genus >= 1 or with >= 2 dots is zero, a closed
component is 1 exactly when it carries one dot, and a planar component with
k boundary circles and d dots is Delta^(k-1)(x^d).  Invertible entries are
cancelled by Gaussian elimination after every crossing, which often reduces the complex substantially. Boundary size alone does
not bound the multiplicity of surviving objects.  The final complex is a complex of
F2-vector spaces with zero differential; its size is the total unreduced
Khovanov rank.  For a knot this rank is 2 exactly for the unknot.

The worst-case upper bound remains exponential. See docs/report.pdf for the
proved connected-sum parameter bound and measured speedups.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from functools import lru_cache
from itertools import product
from heapq import heappop, heappush
from math import isfinite
from time import monotonic
from typing import Any, Iterable

SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))  # 0: (a,b),(c,d)   1: (a,d),(b,c)

Matching = frozenset  # frozenset of frozenset({p, q}) pairs of boundary labels
Morphism = set        # set of frozenset(circle keys); F2 coefficients


class ScanLimit(RuntimeError):
    """A user-selected ceiling was reached; this is never a knot verdict."""


def _dsu_find(parent: dict, x):
    root = x
    while parent[root] != root:
        root = parent[root]
    while parent[x] != root:
        parent[x], x = root, parent[x]
    return root


@lru_cache(maxsize=8192)
def circles(a: Matching, b: Matching) -> dict:
    """Map each boundary label to the key (frozenset of labels) of its circle in a u b~."""
    parent: dict = {}
    for pair in a | b:
        for p in pair:
            parent.setdefault(p, p)
    for pair in a | b:
        p, q = tuple(pair)
        rp, rq = _dsu_find(parent, p), _dsu_find(parent, q)
        if rp != rq:
            parent[rp] = rq
    groups: dict = defaultdict(list)
    for p in parent:
        groups[_dsu_find(parent, p)].append(p)
    keys = {root: frozenset(members) for root, members in groups.items()}
    return {p: keys[_dsu_find(parent, p)] for p in parent}


@dataclass
class Glued:
    """Result of attaching one smoothing of a crossing to a matching."""
    points: frozenset
    matching: Matching
    closed: int                                  # number of closed circles created
    arc_of: dict = field(default_factory=dict)   # arc id -> ('new', pair) | ('closed', index)


@lru_cache(maxsize=8192)
def glue(m: Matching, smoothing_index: int, points: frozenset, slots: tuple) -> Glued:
    """Attach the crossing with edge labels `slots` (counterclockwise) to the region.

    Arc ids are ('m', pair) for arcs of m and ('s', j) for the two smoothing arcs.
    """
    adjacency: dict = defaultdict(list)
    for pair in m:
        p, q = tuple(pair)
        adjacency[('P', p)].append((('P', q), ('m', pair)))
        adjacency[('P', q)].append((('P', p), ('m', pair)))
    for j, (s, t) in enumerate(SMOOTHINGS[smoothing_index]):
        adjacency[('S', s)].append((('S', t), ('s', j)))
        adjacency[('S', t)].append((('S', s), ('s', j)))
    first_slot: dict = {}
    for j, label in enumerate(slots):
        if label in points:
            adjacency[('S', j)].append((('P', label), None))
            adjacency[('P', label)].append((('S', j), None))
        elif label in first_slot:
            j0 = first_slot[label]
            adjacency[('S', j)].append((('S', j0), None))
            adjacency[('S', j0)].append((('S', j), None))
        else:
            first_slot[label] = j

    def label_of(node):
        return node[1] if node[0] == 'P' else slots[node[1]]

    visited: set = set()
    new_pairs, arc_of, closed = [], {}, 0
    ends = [node for node, nbrs in adjacency.items() if len(nbrs) == 1]
    for start in ends:
        if start in visited:
            continue
        node, prev, arcs = start, None, []
        visited.add(node)
        while True:
            step = next(((nbr, arc) for nbr, arc in adjacency[node] if nbr != prev), None)
            if step is None:
                break
            nbr, arc = step
            if arc is not None:
                arcs.append(arc)
            prev, node = node, nbr
            visited.add(node)
            if len(adjacency[node]) == 1:
                break
        pair = frozenset((label_of(start), label_of(node)))
        if len(pair) != 2:
            raise ArithmeticError("degenerate boundary arc")
        new_pairs.append(pair)
        for arc in arcs:
            arc_of[arc] = ('new', pair)
    for start in adjacency:
        if start in visited:
            continue
        node, prev, arcs = start, None, []
        visited.add(node)
        while True:
            options = [(nbr, arc) for nbr, arc in adjacency[node] if nbr != prev]
            if not options:
                break
            nbr, arc = options[0]
            if arc is not None:
                arcs.append(arc)
            prev, node = node, nbr
            if node == start:
                break
            visited.add(node)
        for arc in arcs:
            arc_of[arc] = ('closed', closed)
        closed += 1
    new_points = frozenset(p for pair in new_pairs for p in pair)
    return Glued(new_points, frozenset(new_pairs), closed, arc_of)


def _expand(components: list, dots: list) -> set:
    """Normal form of a surface: set of dot-subsets (product over components)."""
    result = {frozenset()}
    for (boundary, chi), d in zip(components, dots):
        twice_genus = 2 - chi - len(boundary)
        if twice_genus < 0 or twice_genus % 2:
            raise ArithmeticError(f"impossible surface component: chi={chi}, boundary={len(boundary)}")
        if twice_genus or d >= 2:
            return set()
        if not boundary:
            if d == 1:
                continue
            return set()
        if d == 1:
            options = [frozenset(boundary)]
        else:
            options = [frozenset(boundary - {undotted}) for undotted in boundary]
        result = {x | y for x in result for y in options}
    return result


@lru_cache(maxsize=8192)
def _compose_plan(a: Matching, b: Matching, c: Matching):
    """Topology of composition, independent of both morphism coefficients."""
    ab, bc, ac = circles(a, b), circles(b, c), circles(a, c)
    parent: dict = {}
    for key in set(ab.values()):
        parent[('L', key)] = ('L', key)
    for key in set(bc.values()):
        parent[('R', key)] = ('R', key)
    for pair in b:
        p = next(iter(pair))
        x, y = _dsu_find(parent, ('L', ab[p])), _dsu_find(parent, ('R', bc[p]))
        if x != y:
            parent[x] = y
    members: dict = defaultdict(set)
    for disk in parent:
        members[_dsu_find(parent, disk)].add(disk)
    glue_count: dict = defaultdict(int)
    for pair in b:
        glue_count[_dsu_find(parent, ('L', ab[next(iter(pair))]))] += 1
    boundary: dict = defaultdict(set)
    for pair in a:
        p = next(iter(pair))
        boundary[_dsu_find(parent, ('L', ab[p]))].add(ac[p])
    for pair in c:
        p = next(iter(pair))
        boundary[_dsu_find(parent, ('R', bc[p]))].add(ac[p])
    roots = list(members)
    components = tuple((frozenset(boundary[r]), len(members[r]) - glue_count[r]) for r in roots)
    index = {disk: i for i, r in enumerate(roots) for disk in members[r]}
    return components, index


@lru_cache(maxsize=16384)
def _compose_cached(f: frozenset, g: frozenset, a: Matching, b: Matching, c: Matching):
    components, index = _compose_plan(a, b, c)
    result: set = set()
    for tf in f:
        dots_f = [0] * len(components)
        for key in tf:
            dots_f[index[('L', key)]] += 1
        for tg in g:
            dots = dots_f[:]
            for key in tg:
                dots[index[('R', key)]] += 1
            result ^= _expand(components, dots)
    return frozenset(result)



def compose(f: Morphism, g: Morphism, a: Matching, b: Matching, c: Matching) -> Morphism:
    """g o f. Bounded caches and square-free endomorphism multiplication."""
    if not f or not g:
        return set()
    one = frozenset()
    if a == b and len(f) == 1 and one in f:
        return set(g)
    if b == c and len(g) == 1 and one in g:
        return set(f)
    if a == b == c:
        result = set()
        for x in f:
            for y in g:
                if x.isdisjoint(y):
                    term = x | y
                    if term in result:
                        result.remove(term)
                    else:
                        result.add(term)
        return result
    return set(_compose_cached(frozenset(f), frozenset(g), a, b, c))


def identity(m: Matching) -> Morphism:
    return {frozenset()}


def is_unit(f: Morphism) -> bool:
    return frozenset() in f


def inverse(f: Morphism, m: Matching) -> Morphism:
    """Every unit in F2[x_1,...,x_k]/(x_i^2) is its own inverse.

    For f=1+nu, Frobenius gives nu^2=0, so f^2=1. This avoids the
    baseline's geometric-series compositions entirely.
    """
    if not is_unit(f):
        raise ValueError("not a unit")
    return set(f)


@lru_cache(maxsize=8192)
def _crossing_entries_cached(m_src: Matching, m_tgt: Matching, f: Morphism, i_src: int, i_tgt: int,
                     points: frozenset, slots: tuple) -> tuple[Glued, Glued, dict]:
    """Entries of the tensor product with a crossing complex, after delooping.

    Returns the two glued objects and a map (labels_src, labels_tgt) -> morphism,
    where labels are tuples over the closed circles (0 = label 1, 1 = label x).
    """
    gs, gt = glue(m_src, i_src, points, slots), glue(m_tgt, i_tgt, points, slots)
    mm = circles(m_src, m_tgt)
    f_keys = sorted(set(mm.values()), key=sorted)
    disks = [('F', key) for key in f_keys]
    saddle = i_src != i_tgt
    if saddle:
        disks.append(('I', 's'))

        def idisk(side, j):
            return ('I', 's')
    else:
        disks.extend([('I', 0), ('I', 1)])

        def idisk(side, j):
            return ('I', j)
    parent = {d: d for d in disks}
    smoothing_of_slot = []
    for i in (i_src, i_tgt):
        table = {}
        for j, arc in enumerate(SMOOTHINGS[i]):
            for s in arc:
                table[s] = j
        smoothing_of_slot.append(table)
    unions: list = []
    seen_slots: dict = {}
    for j, label in enumerate(slots):
        if label in points:
            unions.append((('F', mm[label]), idisk(0, smoothing_of_slot[0][j])))
        elif label in seen_slots:
            j0 = seen_slots[label]
            unions.append((idisk(0, smoothing_of_slot[0][j0]), idisk(0, smoothing_of_slot[0][j])))
        else:
            seen_slots[label] = j
    for x, y in unions:
        rx, ry = _dsu_find(parent, x), _dsu_find(parent, y)
        if rx != ry:
            parent[rx] = ry
    members: dict = defaultdict(set)
    for d in disks:
        members[_dsu_find(parent, d)].add(d)
    glue_count: dict = defaultdict(int)
    for x, _ in unions:
        glue_count[_dsu_find(parent, x)] += 1
    nn = circles(gs.matching, gt.matching)
    roots = list(members)
    root_index = {r: i for i, r in enumerate(roots)}
    boundary = [set() for _ in roots]
    closed_src: list = [None] * gs.closed
    closed_tgt: list = [None] * gt.closed

    def record(disk, ref, closed_list):
        comp = root_index[_dsu_find(parent, disk)]
        kind, value = ref
        if kind == 'new':
            boundary[comp].add(nn[next(iter(value))])
        else:
            closed_list[value] = comp

    for pair in m_src:
        record(('F', mm[next(iter(pair))]), gs.arc_of[('m', pair)], closed_src)
    for j in range(2):
        record(idisk(0, j), gs.arc_of[('s', j)], closed_src)
    for pair in m_tgt:
        record(('F', mm[next(iter(pair))]), gt.arc_of[('m', pair)], closed_tgt)
    for j in range(2):
        record(idisk(1, j), gt.arc_of[('s', j)], closed_tgt)
    if any(c is None for c in closed_src) or any(c is None for c in closed_tgt):
        raise ArithmeticError("closed circle without a bounding component")
    base_chi = [len(members[r]) - glue_count[r] for r in roots]
    disk_index = {d: root_index[_dsu_find(parent, d)] for d in disks}
    result: dict = {}
    for labels_src in product((0, 1), repeat=gs.closed):
        for labels_tgt in product((0, 1), repeat=gt.closed):
            chi = base_chi[:]
            extra = [0] * len(roots)
            for comp, lab in zip(closed_src, labels_src):
                chi[comp] += 1
                extra[comp] += lab            # x on the source circle: dotted cup
            for comp, lab in zip(closed_tgt, labels_tgt):
                chi[comp] += 1
                extra[comp] += 1 - lab        # coefficient of 1 on the target: dotted cap
            components = [(boundary[i], chi[i]) for i in range(len(roots))]
            morphism: set = set()
            for term in f:
                dots = extra[:]
                for key in term:
                    dots[disk_index[('F', key)]] += 1
                morphism ^= _expand(components, dots)
            if morphism:
                result[labels_src, labels_tgt] = morphism
    return gs, gt, result


def crossing_entries(m_src, m_tgt, f, i_src, i_tgt, points, slots):
    gs, gt, entries = _crossing_entries_cached(
        m_src, m_tgt, frozenset(f), i_src, i_tgt, points, slots)
    # Callers own the returned dictionary and coefficient sets.
    return gs, gt, {labels: set(value) for labels, value in entries.items()}


def clear_scan_caches():
    for function in (circles, glue, _compose_plan, _compose_cached, _crossing_entries_cached):
        function.cache_clear()



@dataclass
class Object:
    matching: Matching
    h: int


class ScanComplex:
    """The partial Khovanov complex of the processed part of a diagram."""

    def __init__(self, max_objects: int | None = None, deadline: float | None = None):
        self.objects: dict[int, Object] = {}
        self.out: dict[int, dict[int, Morphism]] = defaultdict(dict)
        self.inc: dict[int, set[int]] = defaultdict(set)
        self.points: frozenset = frozenset()
        self.next_id = 0
        self.max_objects = max_objects
        self.deadline = deadline
        self.stats = {'max_objects_before_elimination': 0, 'max_objects_after_elimination': 0,
                      'eliminations': 0, 'max_boundary': 0, 'compositions': 0}
        self._new_object(frozenset(), 0)

    def _new_object(self, matching: Matching, h: int) -> int:
        i = self.next_id
        self.next_id += 1
        self.objects[i] = Object(matching, h)
        return i

    def _check(self) -> None:
        if self.deadline is not None and monotonic() > self.deadline:
            raise ScanLimit("time budget exhausted")

    def _set(self, a: int, b: int, morphism: Morphism) -> None:
        if morphism:
            self.out[a][b] = morphism
            self.inc[b].add(a)
        else:
            self.out[a].pop(b, None)
            self.inc[b].discard(a)

    def add_crossing(self, slots: tuple) -> None:
        self._check()
        points, old_objects = self.points, self.objects
        new_id: dict = {}
        glued: dict = {}
        for o, obj in old_objects.items():
            self._check()
            for i in (0, 1):
                g = glue(obj.matching, i, points, slots)
                glued[o, i] = g
                for labels in product((0, 1), repeat=g.closed):
                    new_id[o, i, labels] = None
                    if self.max_objects is not None and len(new_id) > self.max_objects:
                        raise ScanLimit("object ceiling reached before allocation")
        if self.max_objects is not None and len(new_id) > self.max_objects:
            raise ScanLimit(f"{len(new_id)} objects would exceed the ceiling {self.max_objects}")
        objects: dict[int, Object] = {}
        self.objects = objects
        for (o, i, labels) in list(new_id):
            new_id[o, i, labels] = self._new_object(glued[o, i].matching, old_objects[o].h + i)
        old_out = self.out
        self.out, self.inc = defaultdict(dict), defaultdict(set)
        for o, obj in old_objects.items():
            self._check()
            _, _, entries = crossing_entries(obj.matching, obj.matching, identity(obj.matching),
                                             0, 1, points, slots)
            for (ls, lt), morphism in entries.items():
                self._set(new_id[o, 0, ls], new_id[o, 1, lt], morphism)
            for o2, f in old_out[o].items():
                m2 = old_objects[o2].matching
                for i in (0, 1):
                    _, _, entries = crossing_entries(obj.matching, m2, f, i, i, points, slots)
                    for (ls, lt), morphism in entries.items():
                        self._set(new_id[o, i, ls], new_id[o2, i, lt], morphism)
        self.points = next(iter(glued.values())).points if glued else frozenset()
        self.stats['max_objects_before_elimination'] = max(
            self.stats['max_objects_before_elimination'], len(objects))
        self.stats['max_boundary'] = max(self.stats['max_boundary'], len(self.points))
        self.eliminate()
        self.stats['max_objects_after_elimination'] = max(
            self.stats['max_objects_after_elimination'], len(self.objects))

    def _invertible(self, a: int, b: int) -> bool:
        f = self.out[a].get(b)
        return (f is not None and is_unit(f)
                and self.objects[a].matching == self.objects[b].matching)

    def eliminate(self) -> None:
        """Gaussian cancellation with a lazy sparse-fill priority.

        The key (incoming-1)*(outgoing-1) estimates Schur-complement work.
        Lazy priorities are a heuristic, not a claim of global fill optimality.
        Any selected unit gives the same chain-homotopy equivalence.
        """
        heap = []

        def cost(b, c):
            return (len(self.inc[c]) - 1) * (len(self.out[b]) - 1)

        def offer(b, c):
            if self._invertible(b, c):
                heappush(heap, (cost(b, c), b, c))

        for b in list(self.out):
            for c in list(self.out[b]):
                offer(b, c)
        while heap:
            self._check()
            old_cost, b, c = heappop(heap)
            if b not in self.objects or c not in self.objects or not self._invertible(b, c):
                continue
            new_cost = cost(b, c)
            if new_cost > old_cost:
                heappush(heap, (new_cost, b, c))
                continue
            phi_inv = inverse(self.out[b][c], self.objects[b].matching)
            m = self.objects[b].matching
            ins = [(a, self.out[a][c]) for a in self.inc[c] if a != b]
            outs = [(f, self.out[b][f]) for f in self.out[b] if f != c]
            for a, delta in ins:
                self._check()
                ma = self.objects[a].matching
                half = compose(delta, phi_inv, ma, m, m)
                self.stats['compositions'] += 1
                for f, gamma in outs:
                    mf = self.objects[f].matching
                    term = compose(half, gamma, ma, m, mf)
                    self.stats['compositions'] += 1
                    if term:
                        current = self.out[a].get(f, set()) ^ term
                        self._set(a, f, current)
                        if current:
                            offer(a, f)
            # Track neighbours whose fill cost may have decreased.
            affected_sources = set(self.inc[c]) | set(self.inc[b])
            affected_targets = set(self.out[b]) | set(self.out[c])
            for x in (b, c):
                for y in list(self.out[x]):
                    self._set(x, y, set())
                for y in list(self.inc[x]):
                    self._set(y, x, set())
                del self.objects[x]
                self.out.pop(x, None)
                self.inc.pop(x, None)
            self.stats['eliminations'] += 1
            # Refresh surviving incident units. Rebuild if stale entries dominate.
            if len(heap) > 8 * (len(self.objects) + 1) + 1024:
                heap.clear()
                for a in list(self.out):
                    for f in self.out[a]:
                        offer(a, f)
            else:
                for a in affected_sources:
                    if a in self.objects:
                        for f in self.out[a]:
                            offer(a, f)
                for f in affected_targets:
                    if f in self.objects:
                        for a in self.inc[f]:
                            offer(a, f)

    def total_rank(self) -> int:
        if self.points:
            raise ValueError("the diagram is not closed yet")
        if any(self.out[a] for a in list(self.out)):
            raise ArithmeticError("minimal closed complex still has a nonzero differential")
        return len(self.objects)

    def ranks_by_degree(self) -> dict[int, int]:
        counts: dict[int, int] = defaultdict(int)
        for obj in self.objects.values():
            counts[obj.h] += 1
        return dict(sorted(counts.items()))

    def check_d_squared(self) -> None:
        """Debug check: compose consecutive differentials and require zero."""
        for a in list(self.out):
            acc: dict = defaultdict(set)
            ma = self.objects[a].matching
            for b, f in self.out[a].items():
                mb = self.objects[b].matching
                for c, g in self.out[b].items():
                    acc[c] ^= compose(f, g, ma, mb, self.objects[c].matching)
            for c, value in acc.items():
                if value:
                    raise ArithmeticError(f"d^2 != 0 between objects {a} and {c}")


# Same greedy policy as the baseline, now O(n log n) for a fixed number of starts.
from .ordering import scan_order, order_profile, best_scan_order, validate_order


def _rank_one(diagram, *, order, max_objects, deadline, check_d_squared):
    pd = diagram.pd
    if not pd:
        return {'rank': 2, 'reduced_rank': 1, 'by_degree': {0: 2}, 'stats': {}, 'order': []}
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("time budget exhausted")
    order = best_scan_order(pd, tries=min(len(pd), 12)) if order is None else order
    clear_scan_caches()
    try:
        complex_ = ScanComplex(max_objects=max_objects, deadline=deadline)
        for index in order:
            complex_.add_crossing(pd[index])
            if check_d_squared:
                complex_.check_d_squared()
        rank = complex_.total_rank()
        if rank % 2:
            raise ArithmeticError("unreduced knot rank is not even")
        complex_.stats['cache_hits'] = {
            'composition': _compose_cached.cache_info().hits,
            'composition_topology': _compose_plan.cache_info().hits,
            'crossing_entries': _crossing_entries_cached.cache_info().hits}
        return {'rank': rank, 'reduced_rank': rank // 2,
                'by_degree': complex_.ranks_by_degree(), 'stats': complex_.stats, 'order': order}
    finally:
        # Neither successful calls nor resource-limit failures retain old diagrams.
        clear_scan_caches()


def khovanov_rank(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False, factor: bool = True) -> dict[str, Any]:
    """Exact knot rank. Factor diagrammatic connected sums before scanning.

    Explicit order disables factorisation so that exactly that order is used.
    Worst-case 2^O(n) remains; no width-only bound on chain multiplicity is assumed.
    """
    from .diagram import Diagram
    from .factors import diagram_factors
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError("max_objects must be a positive integer or None")
    deadline = None if seconds is None else monotonic() + seconds
    diagram = Diagram.from_pd(pd)
    if order is not None:
        order = validate_order(order, diagram.crossings)
    pieces, proof = ([diagram], None)
    if factor and order is None:
        pieces, proof = diagram_factors(diagram, deadline=deadline)
    if len(pieces) == 1:
        return _rank_one(diagram, order=order, max_objects=max_objects, deadline=deadline,
                         check_d_squared=check_d_squared)
    # Over F2 the unreduced complex splits into two copies of the reduced one.
    # Reduced homology of a connected sum is the tensor product over the field.
    by_degree = {0: 1}
    reports = []
    memo = {}
    for piece in pieces:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")
        reused = piece.pd in memo
        if not reused:
            memo[piece.pd] = _rank_one(piece, order=None, max_objects=max_objects,
                                     deadline=deadline, check_d_squared=check_d_squared)
        report = memo[piece.pd]
        counts = report['by_degree']
        if any(value % 2 for value in counts.values()):
            raise ArithmeticError("unreduced rank in a degree is not even")
        result = defaultdict(int)
        for i, a in by_degree.items():
            for j, b in counts.items():
                result[i+j] += a * (b // 2)
        by_degree = dict(result)
        reports.append({'crossings': piece.crossings, 'reused': reused, **report})
    red_rank = sum(by_degree.values())
    stats = {}
    for key in ('max_objects_before_elimination', 'max_objects_after_elimination', 'max_boundary'):
        stats[key] = max(r['stats'].get(key, 0) for r in reports)
    for key in ('eliminations', 'compositions'):
        stats[key] = sum(r['stats'].get(key, 0) for r in reports if not r['reused'])
    stats['factor_count'] = len(pieces)
    return {'rank': 2*red_rank, 'reduced_rank': red_rank,
            'by_degree': {i: 2*a for i, a in sorted(by_degree.items())},
            'order': None, 'stats': stats, 'factors': reports, 'factor_certificate': proof}
