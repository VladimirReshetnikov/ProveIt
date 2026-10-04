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
cancelled by Gaussian elimination after every crossing, so the complex stays
small when the scan has a small boundary.  The final complex is a complex of
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


def compose(f: Morphism, g: Morphism, a: Matching, b: Matching, c: Matching) -> Morphism:
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


def inverse(f: Morphism, m: Matching) -> Morphism:
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


def crossing_entries(m_src: Matching, m_tgt: Matching, f: Morphism, i_src: int, i_tgt: int,
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


