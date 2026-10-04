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
cancelled by Gaussian elimination after every crossing, which often reduces the
complex in practice. Small boundary alone does not bound homology multiplicities.  The final complex is a complex of
F2-vector spaces with zero differential; its size is the total unreduced
Khovanov rank.  For a knot this rank is 2 exactly for the unknot.

Nothing here is quasi-polynomial: the worst case is still exponential.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from functools import lru_cache
from itertools import product
import heapq
import math
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


@lru_cache(maxsize=16384)
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


@lru_cache(maxsize=16384)
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


def _compose_uncached(f: Morphism, g: Morphism, a: Matching, b: Matching, c: Matching) -> Morphism:
    """g o f for f: a -> b and g: b -> c, as an element of Hom(a, c)."""
    if not f or not g:
        return set()
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
    components = [(boundary[r], len(members[r]) - glue_count[r]) for r in roots]
    index = {disk: i for i, r in enumerate(roots) for disk in members[r]}
    result: set = set()
    for tf in f:
        dots_f = [0] * len(roots)
        for key in tf:
            dots_f[index[('L', key)]] += 1
        for tg in g:
            dots = dots_f[:]
            for key in tg:
                dots[index[('R', key)]] += 1
            result ^= _expand(components, dots)
    return result


def identity(m: Matching) -> Morphism:
    return {frozenset()}


def is_unit(f: Morphism) -> bool:
    return frozenset() in f


def _inverse_reference(f: Morphism, m: Matching) -> Morphism:
    """Inverse of a unit 1 + nu in the local ring End(m)."""
    if not is_unit(f):
        raise ValueError("not a unit")
    nu = set(f)
    nu.discard(frozenset())
    result, power = {frozenset()}, {frozenset()}
    while True:
        power = compose(power, nu, m, m, m)
        if not power:
            return result
        result ^= power


def _crossing_entries_uncached(m_src: Matching, m_tgt: Matching, f: Morphism, i_src: int, i_tgt: int,
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


# Public morphisms retain the baseline set-of-dot-sets representation.  The
# cache stores immutable values; callers get fresh sets/dicts to avoid aliasing.
@lru_cache(maxsize=32768)
def _compose_monomial(tf, tg, a, b, c):
    return frozenset(_compose_uncached({tf}, {tg}, a, b, c))


def compose(f: Morphism, g: Morphism, a: Matching, b: Matching,
            c: Matching) -> Morphism:
    """Compose exactly, using identities, the local ring, and memoized basis products."""
    if not f or not g:
        return set()
    unit = frozenset()
    if a == b and len(f) == 1 and unit in f:
        return set(g)
    if b == c and len(g) == 1 and unit in g:
        return set(f)
    result = set()
    if a == b == c:
        # End(m) = F2[x_1,...,x_r]/(x_1^2,...,x_r^2).
        for left in f:
            for right in g:
                if left.isdisjoint(right):
                    term = left | right
                    if term in result:
                        result.remove(term)
                    else:
                        result.add(term)
        return result
    for left in f:
        for right in g:
            result.symmetric_difference_update(_compose_monomial(left, right, a, b, c))
    return result


def inverse(f: Morphism, m: Matching) -> Morphism:
    """In characteristic two every unit in End(m) is its own inverse."""
    if not is_unit(f):
        raise ValueError("not a unit")
    return set(f)


@lru_cache(maxsize=8192)
def _crossing_entries_cached(m_src, m_tgt, frozen_f, i_src, i_tgt, points, slots):
    gs, gt, entries = _crossing_entries_uncached(
        m_src, m_tgt, frozen_f, i_src, i_tgt, points, slots)
    return gs, gt, tuple((key, frozenset(value)) for key, value in entries.items())


def crossing_entries(m_src: Matching, m_tgt: Matching, f: Morphism,
                     i_src: int, i_tgt: int, points: frozenset,
                     slots: tuple) -> tuple[Glued, Glued, dict]:
    gs, gt, entries = _crossing_entries_cached(
        m_src, m_tgt, frozenset(f), i_src, i_tgt, points, slots)
    return gs, gt, {key: set(value) for key, value in entries}


def clear_caches() -> None:
    """Release process-wide bounded geometry caches (optional, thread-safe to clear)."""
    circles.cache_clear()
    glue.cache_clear()
    _compose_monomial.cache_clear()
    _crossing_entries_cached.cache_clear()


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
                        raise ScanLimit(f"object ceiling {self.max_objects} exceeded")
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
        """Cancel units with a lazy Markowitz heap to discourage differential fill-in.

        Stale scores affect only the heuristic, never the validity of a pivot.
        Any invertible differential entry is a legal chain-homotopy cancellation.
        """
        heap = []

        def score(b, c):
            return (len(self.inc[c]) - 1) * (len(self.out[b]) - 1)

        def enqueue(b, c):
            if self._invertible(b, c):
                heapq.heappush(heap, (score(b, c), b, c))

        for a in list(self.out):
            for b in list(self.out[a]):
                enqueue(a, b)
        while heap:
            self._check()
            cost, b, c = heapq.heappop(heap)
            if b not in self.objects or c not in self.objects or not self._invertible(b, c):
                continue
            new_cost = score(b, c)
            if cost != new_cost:
                heapq.heappush(heap, (new_cost, b, c))
                continue
            phi = self.out[b][c]
            m = self.objects[b].matching
            phi_inv = inverse(phi, m)
            ins = [(a, self.out[a][c]) for a in sorted(self.inc[c]) if a != b]
            outs = [(f, self.out[b][f]) for f in sorted(self.out[b]) if f != c]
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
                        current = set(self.out[a].get(f, set()))
                        current ^= term
                        self._set(a, f, current)
                        if current:
                            enqueue(a, f)
            for x in (b, c):
                for y in list(self.out[x]):
                    self._set(x, y, set())
                for y in list(self.inc[x]):
                    self._set(y, x, set())
                del self.objects[x]
                self.out.pop(x, None)
                self.inc.pop(x, None)
            self.stats['eliminations'] += 1

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
            self._check()
            acc: dict = defaultdict(set)
            ma = self.objects[a].matching
            for b, f in self.out[a].items():
                self._check()
                mb = self.objects[b].matching
                for c, g in self.out[b].items():
                    acc[c] ^= compose(f, g, ma, mb, self.objects[c].matching)
            for c, value in acc.items():
                if value:
                    raise ArithmeticError(f"d^2 != 0 between objects {a} and {c}")


def scan_order(pd: list, start: int | None = None) -> list[int]:
    """Baseline's greedy order in O(n log n) rather than O(n^2) time.

    All candidates see the same current boundary size, so the old score reduces
    to (number of shared edges, number of self-loops, -index).  Only the at most
    four neighbours of a newly processed crossing need a heap update.
    """
    n = len(pd)
    if not n:
        return []
    first = 0 if start is None else start
    if type(first) is not int or not 0 <= first < n:
        raise ValueError("invalid starting crossing")
    owners = defaultdict(list)
    for i, row in enumerate(pd):
        for edge in row:
            owners[edge].append(i)
    neighbours = [[] for _ in pd]
    for ends in owners.values():
        if len(ends) != 2:
            raise ValueError("every edge must occur twice")
        a, b = ends
        if a != b:
            neighbours[a].append(b)
            neighbours[b].append(a)
    loops = [4 - len(set(row)) for row in pd]
    shared = [0] * n
    done = [False] * n
    heap = [(0, -loops[i], i) for i in range(n)]
    heapq.heapify(heap)
    order = []
    current = first
    for step in range(n):
        if step:
            while heap:
                old_score, _, current = heapq.heappop(heap)
                if not done[current] and old_score == -shared[current]:
                    break
        done[current] = True
        order.append(current)
        for neighbour in neighbours[current]:
            if not done[neighbour]:
                shared[neighbour] += 1
                heapq.heappush(heap, (-shared[neighbour], -loops[neighbour], neighbour))
    return order


def order_profile(pd: list, order: list[int]) -> tuple[int, int]:
    """(maximal boundary size, total boundary size) along an order."""
    boundary: set = set()
    worst = total = 0
    for i in order:
        for e in pd[i]:
            boundary.symmetric_difference_update({e})
        worst = max(worst, len(boundary))
        total += len(boundary)
    return worst, total


def best_scan_order(pd: list, tries: int | None = None) -> list[int]:
    """Greedy orders from several starting crossings; keep the smallest boundary profile."""
    n = len(pd)
    if n == 0:
        return []
    if tries is not None and (type(tries) is not int or tries < 1):
        raise ValueError("tries must be a positive integer")
    starts = range(n) if tries is None or tries >= n else range(0, n, max(1, n // tries))
    best, best_profile = None, None
    for start in starts:
        order = scan_order(pd, start)
        profile = order_profile(pd, order)
        if best_profile is None or profile < best_profile:
            best, best_profile = order, profile
    return best


def _khovanov_rank_scan(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False) -> dict[str, Any]:
    """Total unreduced F2 Khovanov rank of a (validated) PD code by scanning."""
    pd = [tuple(c) for c in pd]
    if seconds is not None and (not math.isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError("max_objects must be a positive integer")
    if order is not None and (len(order) != len(pd)
                             or any(type(i) is not int for i in order)
                             or sorted(order) != list(range(len(pd)))):
        raise ValueError("order must be a permutation of all crossing indices")
    deadline = None if seconds is None else monotonic() + seconds
    if not pd:
        return {'rank': 2, 'reduced_rank': 1, 'by_degree': {0: 2}, 'stats': {}, 'order': []}
    order = best_scan_order(pd, tries=min(len(pd), 12)) if order is None else list(order)
    complex_ = ScanComplex(max_objects=max_objects, deadline=deadline)
    for index in order:
        complex_.add_crossing(pd[index])
        if check_d_squared:
            complex_.check_d_squared()
    rank = complex_.total_rank()
    return {'rank': rank, 'reduced_rank': rank // 2, 'by_degree': complex_.ranks_by_degree(),
            'stats': complex_.stats, 'order': order}


def khovanov_rank(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False, factor: bool = True) -> dict[str, Any]:
    """Exact F2 ranks, factoring visible connected sums before scanning.

    Supplying an explicit order disables factorization: the supplied order is
    then used literally.  `factor=False` isolates the accelerated scan kernel.
    The same object cap applies separately to every factor, never to the integer
    value of the returned homology rank.  Rank can be exponentially larger than
    the stored factored answer.
    """
    from .diagram import Diagram
    from .decompose import factor_diagram
    pd = [tuple(c) for c in pd]
    if seconds is not None and (not math.isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError("max_objects must be a positive integer")
    deadline = None if seconds is None else monotonic() + seconds
    if not factor or order is not None or not pd:
        return _khovanov_rank_scan(pd, order=order, max_objects=max_objects, seconds=seconds,
                                  check_d_squared=check_d_squared)
    diagram = Diagram.from_pd(pd)
    factors, trace = factor_diagram(diagram, deadline)
    def remaining():
        return None if deadline is None else max(0.0, deadline - monotonic())
    if len(factors) == 1:
        return _khovanov_rank_scan(pd, max_objects=max_objects, seconds=remaining(),
                                  check_d_squared=check_d_squared)
    polynomial = {0: 1}
    details = []
    stats = {'max_objects_before_elimination': 0, 'max_objects_after_elimination': 0,
             'eliminations': 0, 'max_boundary': 0, 'compositions': 0,
             'factor_count': len(factors)}
    for component in factors:
        result = _khovanov_rank_scan(component.pd, max_objects=max_objects, seconds=remaining(),
                                    check_d_squared=check_d_squared)
        degrees = result['by_degree']
        if any(count % 2 for count in degrees.values()):
            raise ArithmeticError("unreduced F2 knot ranks must be even in every homological degree")
        product_degrees = defaultdict(int)
        for h, coefficient in polynomial.items():
            for k, count in degrees.items():
                product_degrees[h + k] += coefficient * (count // 2)
        polynomial = dict(product_degrees)
        for name, value in result['stats'].items():
            stats[name] = (stats.get(name, 0) + value if name in ('eliminations', 'compositions')
                           else max(stats.get(name, 0), value))
        details.append({'pd': [list(c) for c in component.pd], 'order': result['order'],
                        'reduced_rank': result['reduced_rank']})
    reduced_rank = sum(polynomial.values())
    return {'rank': 2 * reduced_rank, 'reduced_rank': reduced_rank,
            'by_degree': {h: 2 * count for h, count in sorted(polynomial.items())},
            'stats': stats, 'order': [], 'factor_details': details, 'split_trace': trace}
