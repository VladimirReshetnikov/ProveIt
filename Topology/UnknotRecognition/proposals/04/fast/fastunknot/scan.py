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
cancelled by Gaussian elimination after every crossing. A small scan boundary
often helps, but does not bound surviving object multiplicities polynomially.  The final complex is a complex of
F2-vector spaces with zero differential; its size is the total unreduced
Khovanov rank.  For a knot this rank is 2 exactly for the unknot.

Nothing here is quasi-polynomial: the worst case is still exponential.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from functools import lru_cache
from itertools import product
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


@lru_cache(maxsize=4096)
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


@lru_cache(maxsize=4096)
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


@lru_cache(maxsize=4096)
def composition_plan(a: Matching, b: Matching, c: Matching):
    """Topological part of composition; independent of dot decorations."""
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
    return components, index, len(roots)


@lru_cache(maxsize=16384)
def _compose_cached(f: frozenset, g: frozenset,
                    a: Matching, b: Matching, c: Matching) -> frozenset:
    if not f or not g:
        return frozenset()
    one = frozenset({frozenset()})
    if a == b and f == one:
        return g
    if b == c and g == one:
        return f
    result: set = set()
    if a == b == c:
        # End(m) = F2[x_1,...,x_r]/(x_1^2,...,x_r^2).
        for tf in f:
            for tg in g:
                if tf.isdisjoint(tg):
                    term = tf | tg
                    if term in result:
                        result.remove(term)
                    else:
                        result.add(term)
        return frozenset(result)
    components, index, count = composition_plan(a, b, c)
    for tf in f:
        dots_f = [0] * count
        for key in tf:
            dots_f[index['L', key]] += 1
        for tg in g:
            dots = dots_f[:]
            for key in tg:
                dots[index['R', key]] += 1
            result ^= _expand(components, dots)
    return frozenset(result)


def compose(f: Morphism, g: Morphism, a: Matching, b: Matching, c: Matching) -> Morphism:
    """g o f, with immutable cached values and fresh mutable public results."""
    return set(_compose_cached(frozenset(f), frozenset(g), a, b, c))


def identity(m: Matching) -> Morphism:
    return {frozenset()}


def is_unit(f: Morphism) -> bool:
    return frozenset() in f


def inverse(f: Morphism, m: Matching) -> Morphism:
    """Every unit is its own inverse in this characteristic-two local ring.

    If f=1+nu and nu has zero constant term, Frobenius gives nu^2=0:
    every nonconstant squarefree monomial has square zero. Thus f^2=1.
    """
    if not is_unit(f):
        raise ValueError("not a unit")
    return set(f)


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


@lru_cache(maxsize=8192)
def _crossing_entries_cached(m_src, m_tgt, f, i_src, i_tgt, points, slots):
    gs, gt, entries = _crossing_entries_uncached(
        m_src, m_tgt, f, i_src, i_tgt, points, slots)
    return gs, gt, tuple((key, frozenset(value)) for key, value in entries.items())


def crossing_entries(m_src, m_tgt, f, i_src, i_tgt, points, slots):
    gs, gt, entries = _crossing_entries_cached(
        m_src, m_tgt, frozenset(f), i_src, i_tgt, points, slots)
    return gs, gt, {key: set(value) for key, value in entries}


def clear_caches() -> None:
    """Bounded caches may also be cleared between independent jobs/benchmarks."""
    for function in (circles, glue, composition_plan, _compose_cached,
                     _crossing_entries_cached):
        function.cache_clear()


def cache_info() -> dict:
    return {function.__name__: function.cache_info()._asdict()
            for function in (circles, glue, composition_plan, _compose_cached,
                             _crossing_entries_cached)}


@dataclass
class Object:
    matching: Matching
    h: int


class ScanComplex:
    """The partial Khovanov complex of the processed part of a diagram."""

    def __init__(self, max_objects: int | None = None, deadline: float | None = None,
                 pivot_strategy: str = "minfill"):
        if pivot_strategy not in ("minfill", "stack"):
            raise ValueError("pivot_strategy must be minfill or stack")
        self.pivot_strategy = pivot_strategy
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
                        raise ScanLimit(f"objects would exceed the ceiling {self.max_objects}")
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
        """Cancel available unit entries by Bar-Natan's Gaussian elimination lemma."""
        from heapq import heapify, heappush, heappop
        def score(a, b):
            ins, outs = len(self.inc[b]) - 1, len(self.out[a]) - 1
            return (ins * outs, ins + outs, a, b)
        queue = [score(a, b) for a in list(self.out) for b in list(self.out[a])
                 if self._invertible(a, b)]
        if self.pivot_strategy == "minfill":
            heapify(queue)
        while queue:
            self._check()
            entry = heappop(queue) if self.pivot_strategy == "minfill" else queue.pop()
            _, _, b, c = entry
            if b not in self.objects or c not in self.objects or not self._invertible(b, c):
                continue
            if self.pivot_strategy == "minfill":
                updated = score(b, c)
                # Lazy priorities: refresh a stale underestimate. A stale
                # overestimate may be accepted. This is a heuristic, not an
                # assertion that the globally cheapest pivot is always used.
                if updated[:2] > entry[:2]:
                    heappush(queue, updated)
                    continue
            phi = self.out[b][c]
            m = self.objects[b].matching
            phi_inv = inverse(phi, m)
            ins = [(a, self.out[a][c]) for a in self.inc[c] if a != b]
            outs = [(f, self.out[b][f]) for f in self.out[b] if f != c]
            for a, delta in (ins if outs else []):
                ma = self.objects[a].matching
                half = compose(delta, phi_inv, ma, m, m)
                self.stats['compositions'] += 1
                for f, gamma in outs:
                    self._check()
                    mf = self.objects[f].matching
                    term = compose(half, gamma, ma, m, mf)
                    self.stats['compositions'] += 1
                    if term:
                        current = set(self.out[a].get(f, set()))
                        current ^= term
                        self._set(a, f, current)
                        if current and self._invertible(a, f):
                            if self.pivot_strategy == "minfill":
                                heappush(queue, score(a, f))
                            else:
                                queue.append(score(a, f))
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
            acc: dict = defaultdict(set)
            ma = self.objects[a].matching
            for b, f in self.out[a].items():
                mb = self.objects[b].matching
                for c, g in self.out[b].items():
                    acc[c] ^= compose(f, g, ma, mb, self.objects[c].matching)
            for c, value in acc.items():
                if value:
                    raise ArithmeticError(f"d^2 != 0 between objects {a} and {c}")


def scan_order(pd: list, start: int | None = None) -> list[int]:
    """Same greedy priorities as the baseline, implemented in O(n log n).

    Shared boundary edges of an unprocessed crossing increase only when one
    of its neighbours is processed. Each edge causes at most one heap update.
    """
    from heapq import heappush, heappop
    n = len(pd)
    if n == 0:
        return []
    current = 0 if start is None else start
    if type(current) is not int or not 0 <= current < n:
        raise ValueError("invalid starting crossing")
    edge_vertices: dict = defaultdict(list)
    for i, row in enumerate(pd):
        for edge in row:
            edge_vertices[edge].append(i)
    neighbours: list[dict] = [defaultdict(int) for _ in pd]
    for ends in edge_vertices.values():
        if len(ends) != 2:
            raise ValueError("each edge must have two ends")
        u, v = ends
        if u != v:
            neighbours[u][v] += 1
            neighbours[v][u] += 1
    shared = [0] * n
    loops = [4 - len(set(row)) for row in pd]
    done = [False] * n
    heap = []
    for i in range(n):
        heappush(heap, (0, -loops[i], i))
    order = []
    while len(order) < n:
        if order:
            while heap:
                negative, _, current = heappop(heap)
                if not done[current] and -negative == shared[current]:
                    break
            else:
                raise ArithmeticError("empty scan-order heap")
        order.append(current)
        done[current] = True
        for neighbour, multiplicity in neighbours[current].items():
            if not done[neighbour]:
                shared[neighbour] += multiplicity
                heappush(heap, (-shared[neighbour], -loops[neighbour], neighbour))
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
    if tries is not None and (type(tries) is not int or tries < 0 or (tries == 0 and n)):
        raise ValueError("tries must be positive for a nonempty diagram")
    if n == 0:
        return []
    starts = range(n) if tries is None or tries >= n else range(0, n, max(1, n // tries))
    best, best_profile = None, None
    for start in starts:
        order = scan_order(pd, start)
        profile = order_profile(pd, order)
        if best_profile is None or profile < best_profile:
            best, best_profile = order, profile
    return best


def khovanov_rank(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False,
                  pivot_strategy: str = "minfill") -> dict[str, Any]:
    """Total unreduced F2 Khovanov rank of a (validated) PD code by scanning."""
    from .diagram import Diagram
    import math
    if seconds is not None and (not math.isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError("max_objects must be a positive integer")
    deadline = None if seconds is None else monotonic() + seconds
    pd = list(Diagram.from_pd(pd).pd)
    if order is not None:
        order = list(order)
        if (any(type(i) is not int for i in order)
                or sorted(order) != list(range(len(pd)))):
            raise ValueError("order must be a permutation of all crossing indices")
    if deadline is not None and monotonic() >= deadline:
        raise ScanLimit("time budget exhausted")
    if not pd:
        return {'rank': 2, 'reduced_rank': 1, 'by_degree': {0: 2}, 'stats': {}, 'order': []}
    order = best_scan_order(pd, tries=min(len(pd), 12)) if order is None else list(order)
    complex_ = ScanComplex(max_objects=max_objects, deadline=deadline,
                           pivot_strategy=pivot_strategy)
    for index in order:
        complex_.add_crossing(pd[index])
        if check_d_squared:
            complex_.check_d_squared()
    rank = complex_.total_rank()
    complex_.stats["pivot_strategy"] = pivot_strategy
    complex_.stats["cache_info"] = cache_info()
    return {'rank': rank, 'reduced_rank': rank // 2, 'by_degree': complex_.ranks_by_degree(),
            'stats': complex_.stats, 'order': order}
