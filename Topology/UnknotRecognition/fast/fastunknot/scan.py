"""Khovanov homology over F2 by scanning (Bar-Natan's local algorithm), version 0.2.

The mathematics is unchanged from 0.1 (see ``scan_reference``): the diagram is
processed crossing by crossing, closed circles are delooped, invertible entries
are cancelled, and the closed minimal complex has zero differential, so its
size is the unreduced rank.  What changed, following the nine acceleration
proposals and measured in the synthesis report:

* min-fill (Markowitz) pivot choice through a lazy heap instead of LIFO;
* every unit of End(m) over F2 is its own inverse, so no geometric series;
* bit-packed morphisms with compiled gluing plans (``algebra.BitAlgebra``);
* heap-based greedy ordering (``ordering``);
* optionally, no cancellation during the last ``tail`` crossings and one F2
  linear-algebra rank computation on the closed complex instead.

``algebra="sets"`` and ``pivot="lifo"`` reproduce the 0.1 behaviour for
ablation.  The worst case remains exponential.
"""
from __future__ import annotations

from collections import defaultdict
from heapq import heappop, heappush
from itertools import product
from time import monotonic
from typing import Any, Iterable

from . import scan_reference as _ref
from .algebra import BitAlgebra
from .geometry import Matching, ScanLimit
from .ordering import best_scan_order, order_profile, scan_order, validate_order
from .scan_fast import FastScan

# set-based helpers kept for compatibility and tests
compose, identity, is_unit = _ref.compose, _ref.identity, _ref.is_unit


def inverse(f, m: Matching):
    """Set-based inverse of a unit of End(m): over F2 a unit is an involution."""
    if not is_unit(f):
        raise ValueError("not a unit")
    return set(f)


class SetAlgebra:
    """Adapter exposing the 0.1 set-based algebra through the BitAlgebra interface."""

    zero = frozenset()
    one = frozenset({frozenset()})

    def __init__(self, check=lambda: None, self_inverse: bool = True):
        self.self_inverse = self_inverse
        self.stats = {"compose_calls": 0}

    def clear(self) -> None:
        pass

    def is_unit(self, f) -> bool:
        return frozenset() in f

    def compose(self, f, g, a, b, c):
        self.stats["compose_calls"] += 1
        return _ref.compose(f, g, a, b, c)

    def inverse(self, f, m):
        return set(f) if self.self_inverse else _ref.inverse(set(f), m)

    def gluing(self, m, i, points, slots):
        return _ref.glue(m, i, points, slots)

    def crossing_entries(self, a, b, f, i_src, i_tgt, points, slots):
        gs, gt, entries = _ref.crossing_entries(a, b, set(f), i_src, i_tgt, points, slots)
        return gs, gt, tuple((ls, lt, value) for (ls, lt), value in entries.items())


class ScanComplex:
    """The partial Khovanov complex of the processed part of a diagram."""

    def __init__(self, max_objects: int | None = None, deadline: float | None = None,
                 pivot: str = "minfill", algebra: str = "bits", self_inverse: bool = True):
        if pivot not in ("minfill", "lifo"):
            raise ValueError("pivot must be 'minfill' or 'lifo'")
        if algebra not in ("bits", "sets"):
            raise ValueError("algebra must be 'bits' or 'sets'")
        if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
            raise ValueError("max_objects must be a nonnegative integer")
        self.objects: dict[int, tuple[Matching, int]] = {}
        self.out: dict[int, dict[int, Any]] = defaultdict(dict)
        self.inc: dict[int, set[int]] = defaultdict(set)
        self.points: frozenset = frozenset()
        self.next_id = 0
        self.max_objects, self.deadline, self.pivot = max_objects, deadline, pivot
        self.algebra = (BitAlgebra(self._check, self_inverse=self_inverse) if algebra == "bits"
                        else SetAlgebra(self._check, self_inverse=self_inverse))
        self.stats = {"max_objects_before_elimination": 0, "max_objects_after_elimination": 0,
                      "eliminations": 0, "max_boundary": 0, "compositions": 0}
        self.objects[self._new_id()] = (frozenset(), 0)

    def _new_id(self) -> int:
        self.next_id += 1
        return self.next_id - 1

    def _check(self) -> None:
        if self.deadline is not None and monotonic() > self.deadline:
            raise ScanLimit("time budget exhausted")

    def _set(self, a: int, b: int, value) -> None:
        if value:
            self.out[a][b] = value
            self.inc[b].add(a)
        else:
            self.out[a].pop(b, None)
            self.inc[b].discard(a)

    # ----- one crossing --------------------------------------------------
    def add_crossing(self, slots: tuple, reduce_now: bool = True) -> None:
        self._check()
        alg = self.algebra
        alg.clear()
        points, old, old_out = self.points, self.objects, self.out
        new_id: dict = {}
        glued: dict = {}
        count = 0
        for o, (matching, h) in old.items():
            for i in (0, 1):
                g = alg.gluing(matching, i, points, slots)
                glued[o, i] = g
                count += 1 << g.closed
        if self.max_objects is not None and count > self.max_objects:
            raise ScanLimit(f"{count} objects would exceed the ceiling {self.max_objects}")
        self.objects = {}
        for (o, i), g in glued.items():
            for labels in product((0, 1), repeat=g.closed):
                ident = self._new_id()
                new_id[o, i, labels] = ident
                self.objects[ident] = (g.matching, old[o][1] + i)
        self.out, self.inc = defaultdict(dict), defaultdict(set)
        one = alg.one
        for o, (matching, _) in old.items():
            self._check()
            for ls, lt, value in alg.crossing_entries(matching, matching, one, 0, 1, points, slots)[2]:
                self._set(new_id[o, 0, ls], new_id[o, 1, lt], value)
            for o2, f in old_out.get(o, {}).items():
                m2 = old[o2][0]
                for i in (0, 1):
                    for ls, lt, value in alg.crossing_entries(matching, m2, f, i, i, points, slots)[2]:
                        self._set(new_id[o, i, ls], new_id[o2, i, lt], value)
        self.points = next(iter(glued.values())).points if glued else frozenset()
        stats = self.stats
        stats["max_objects_before_elimination"] = max(stats["max_objects_before_elimination"], len(self.objects))
        stats["max_boundary"] = max(stats["max_boundary"], len(self.points))
        if reduce_now:
            self.eliminate()
            stats["max_objects_after_elimination"] = max(stats["max_objects_after_elimination"], len(self.objects))

    # ----- Gaussian elimination -------------------------------------------
    def _invertible(self, a: int, b: int) -> bool:
        f = self.out.get(a, {}).get(b)
        return f is not None and self.algebra.is_unit(f) and self.objects[a][0] == self.objects[b][0]

    def _cost(self, a: int, b: int) -> int:
        """Markowitz count: number of differential entries the cancellation can touch."""
        return (len(self.out[a]) - 1) * (len(self.inc[b]) - 1)

    def eliminate(self) -> None:
        """Cancel invertible entries until none is left (Bar-Natan's lemma).

        With ``pivot='minfill'`` the cheapest pivot is taken first.  Priorities
        can be stale; a popped entry whose cost changed is pushed back.  The
        order only affects speed: every unit entry is eventually considered.
        """
        lifo = self.pivot == "lifo"
        alg, objects, out, inc = self.algebra, self.objects, self.out, self.inc
        queue: list = []
        for a in list(out):
            for b in out[a]:
                if self._invertible(a, b):
                    if lifo:
                        queue.append((a, b))
                    else:
                        heappush(queue, (self._cost(a, b), a, b))
        while queue:
            self._check()
            if lifo:
                b, c = queue.pop()
            else:
                cost, b, c = heappop(queue)
            if b not in objects or c not in objects or not self._invertible(b, c):
                continue
            if not lifo and cost != self._cost(b, c):
                heappush(queue, (self._cost(b, c), b, c))
                continue
            m = objects[b][0]
            phi_inv = alg.inverse(out[b][c], m)
            ins = [(a, out[a][c]) for a in inc[c] if a != b]
            outs = [(f, value) for f, value in out[b].items() if f != c]
            for a, delta in ins:
                ma = objects[a][0]
                half = alg.compose(delta, phi_inv, ma, m, m)
                self.stats["compositions"] += 1
                if not half:
                    continue
                row = out[a]
                for f, gamma in outs:
                    term = alg.compose(half, gamma, ma, m, objects[f][0])
                    self.stats["compositions"] += 1
                    if term:
                        current = row.get(f, alg.zero) ^ term
                        self._set(a, f, current)
                        if current and self._invertible(a, f):
                            if lifo:
                                queue.append((a, f))
                            else:
                                heappush(queue, (self._cost(a, f), a, f))
            for x in (b, c):
                for y in list(out[x]):
                    self._set(x, y, alg.zero)
                for y in list(inc[x]):
                    self._set(y, x, alg.zero)
                del objects[x]
                out.pop(x, None)
                inc.pop(x, None)
            self.stats["eliminations"] += 1

    # ----- closing ---------------------------------------------------------
    def linear_ranks(self) -> dict[int, int]:
        """Homology dimensions of the closed complex by F2 linear algebra.

        Used when the last crossings were added without cancellation.  Entries
        of a closed complex are scalars, so each differential is a 0/1 matrix.
        """
        if self.points:
            raise ValueError("the diagram is not closed yet")
        by_degree: dict[int, list[int]] = defaultdict(list)
        for ident, (_, h) in self.objects.items():
            by_degree[h].append(ident)
        rank: dict[int, int] = {}
        for h, sources in by_degree.items():
            index = {ident: k for k, ident in enumerate(by_degree.get(h + 1, []))}
            pivots: dict[int, int] = {}
            for a in sources:
                self._check()
                column = 0
                for b, value in self.out.get(a, {}).items():
                    if value:
                        column |= 1 << index[b]
                while column:
                    top = column.bit_length() - 1
                    if top not in pivots:
                        pivots[top] = column
                        break
                    column ^= pivots[top]
            rank[h] = len(pivots)
        result = {}
        for h, sources in by_degree.items():
            dimension = len(sources) - rank.get(h, 0) - rank.get(h - 1, 0)
            if dimension < 0:
                raise ArithmeticError("negative homology dimension")
            if dimension:
                result[h] = dimension
        return dict(sorted(result.items()))

    def total_rank(self) -> int:
        if self.points:
            raise ValueError("the diagram is not closed yet")
        if any(self.out[a] for a in list(self.out)):
            raise ArithmeticError("minimal closed complex still has a nonzero differential")
        return len(self.objects)

    def ranks_by_degree(self) -> dict[int, int]:
        counts: dict[int, int] = defaultdict(int)
        for _, h in self.objects.values():
            counts[h] += 1
        return dict(sorted(counts.items()))

    def check_d_squared(self) -> None:
        alg = self.algebra
        for a in list(self.out):
            acc: dict = {}
            ma = self.objects[a][0]
            for b, f in self.out[a].items():
                mb = self.objects[b][0]
                for c, g in self.out.get(b, {}).items():
                    acc[c] = acc.get(c, alg.zero) ^ alg.compose(f, g, ma, mb, self.objects[c][0])
            for c, value in acc.items():
                if value:
                    raise ArithmeticError(f"d^2 != 0 between objects {a} and {c}")


def khovanov_rank(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False, pivot: str = "minfill", algebra: str = "bits",
                  self_inverse: bool = True, tail: int = 0, shape_cache: bool = True) -> dict[str, Any]:
    """Total unreduced F2 Khovanov rank of a validated PD code by scanning.

    ``tail`` crossings at the end are added without cancellation and the closed
    complex is finished by linear algebra.  An explicit ``order`` must be a
    permutation of the crossings.  ``shape_cache`` (default scanner only) reuses
    transfer plans across crossings by label-independent shape: about 40% faster
    on periodic diagrams such as torus braids, about 5% slower on small diagrams
    without repeats, not measurable on large ones; results are identical.
    """
    pd = [tuple(c) for c in pd]
    if type(tail) is not int or tail < 0:
        raise ValueError("tail must be a nonnegative integer")
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        return {"rank": 2, "reduced_rank": 1, "by_degree": {0: 2}, "stats": {}, "order": []}
    deadline = None if seconds is None else monotonic() + seconds
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12))
    if pivot == "minfill" and algebra == "bits" and self_inverse:
        complex_ = FastScan(max_objects=max_objects, deadline=deadline, shape_cache=shape_cache)
    else:                         # ablation configurations
        complex_ = ScanComplex(max_objects=max_objects, deadline=deadline, pivot=pivot,
                               algebra=algebra, self_inverse=self_inverse)
    n = len(order)
    for position, index in enumerate(order):
        reduce_now = position < n - tail
        complex_.add_crossing(pd[index], reduce_now=reduce_now)
        if check_d_squared:
            complex_.check_d_squared()
    if tail:
        by_degree = complex_.linear_ranks()
        rank = sum(by_degree.values())
    else:
        rank = complex_.total_rank()
        by_degree = complex_.ranks_by_degree()
    if rank % 2:
        raise ArithmeticError("odd unreduced F2 rank for a knot")
    stats = dict(complex_.stats)
    stats.update({k: v for k, v in complex_.algebra.stats.items()})
    return {"rank": rank, "reduced_rank": rank // 2, "by_degree": by_degree, "stats": stats,
            "order": order, "pivot": pivot, "algebra": algebra, "tail": tail}
