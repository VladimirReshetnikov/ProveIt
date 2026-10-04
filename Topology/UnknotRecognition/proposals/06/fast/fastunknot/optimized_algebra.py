"""Exact immutable F2 cobordisms with bounded, stage-local memoization.

The reference_algebra module is retained as the original implementation of
surface formulas (the geometry helpers remain shared) for differential testing. Returned morphisms and cached
entry values are immutable: callers may never mutate a cached result.
"""
from __future__ import annotations
from collections import defaultdict
from functools import lru_cache
from itertools import product
from .reference_algebra import (Matching, Morphism, ScanLimit, Glued, glue,
                                circles, _dsu_find, _expand, SMOOTHINGS)

EMPTY = frozenset()
ONE = frozenset({frozenset()})
CACHE_SIZE = 16384

def identity(m: Matching) -> Morphism:
    return ONE

def is_unit(f: Morphism) -> bool:
    return frozenset() in f

def inverse(f: Morphism, m: Matching) -> Morphism:
    # In F2[x_1,...,x_k]/(x_i^2), every augmentation-zero element squares
    # to zero. Thus every unit is its own inverse. No geometric series.
    if not is_unit(f):
        raise ValueError("not a unit")
    return frozenset(f)

def compose(f: Morphism, g: Morphism, a: Matching, b: Matching,
            c: Matching) -> Morphism:
    if not f or not g:
        return EMPTY
    f, g = frozenset(f), frozenset(g)
    if a == b and f == ONE:
        return g
    if b == c and g == ONE:
        return f
    return _compose_cached(f, g, a, b, c)

@lru_cache(maxsize=CACHE_SIZE)
def _composition_plan(a, b, c):
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

@lru_cache(maxsize=CACHE_SIZE)
def _compose_cached(f, g, a, b, c):
    if a == b == c:
        # End(a) is a tensor product of dual-number algebras.
        result = set()
        for x in f:
            for y in g:
                if x.isdisjoint(y):
                    term = x | y
                    if term in result:
                        result.remove(term)
                    else:
                        result.add(term)
        return frozenset(result)
    components, index, count = _composition_plan(a, b, c)
    result: set = set()
    for tf in f:
        dots_f = [0] * count
        for key in tf:
            dots_f[index[('L', key)]] += 1
        for tg in g:
            dots = dots_f[:]
            for key in tg:
                dots[index[('R', key)]] += 1
            result ^= _expand(components, dots)
    return frozenset(result)


def crossing_entries(m_src, m_tgt, f, i_src, i_tgt, points, slots):
    return _crossing_entries_cached(m_src, m_tgt, frozenset(f),
                                    i_src, i_tgt, points, slots)

@lru_cache(maxsize=CACHE_SIZE)
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
                result[labels_src, labels_tgt] = frozenset(morphism)
    return gs, gt, result



def clear_caches():
    """Release all old-boundary data. Concurrent clears affect speed only."""
    _composition_plan.cache_clear()
    _compose_cached.cache_clear()
    _crossing_entries_cached.cache_clear()
    circles.cache_clear()
    glue.cache_clear()

def cache_statistics():
    return {name: fun.cache_info()._asdict() for name, fun in
            (("plans", _composition_plan), ("compositions", _compose_cached),
             ("crossings", _crossing_entries_cached), ("circles", circles),
             ("glue", glue))}
