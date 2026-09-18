"""The default scanner: the mathematics of ``scan.ScanComplex`` with the bookkeeping
rewritten for CPython.

Profiling 0.2 showed that the cobordism algebra was no longer the bottleneck;
method calls, tuple-keyed dictionaries and hashing of nested frozensets were.
Here

* matchings are interned as small integers, so every cache key is a tuple of ints;
* objects of a stage are numbered 0..N-1 and live in lists, not dictionaries;
* the objects created from one old object are a contiguous block, so a delooping
  label is an offset and no ``(object, smoothing, labels)`` dictionary is needed;
* transfers of an edge are cached per (source matching, target matching, value)
  for both smoothings at once;
* cancellation is one inlined loop; a stale heap priority is pushed back only
  when the pivot became more expensive than the next candidate.

Only the configuration bits / min-fill / self-inverse is handled; the ablation
configurations stay on ``scan.ScanComplex``.  Results are identical.
"""
from __future__ import annotations

from collections import defaultdict
from heapq import heapify, heappop, heappush
from time import monotonic

from .algebra import BitAlgebra, bits, evaluate
from .geometry import ScanLimit


CAP = 256     # Markowitz costs below this use bucket lists, the rest a heap


class FastScan:
    def __init__(self, max_objects: int | None = None, deadline: float | None = None):
        if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
            raise ValueError("max_objects must be a nonnegative integer")
        self.max_objects, self.deadline = max_objects, deadline
        self.algebra = BitAlgebra(self._check)
        self.matchings: list = [frozenset()]          # id -> matching
        self.ids: dict = {frozenset(): 0}             # matching -> id
        self.mid: list = [0]                          # object -> matching id (None when cancelled)
        self.deg: list = [0]                          # object -> homological degree
        self.out: list = [{}]                         # object -> {target: value}
        self.inc: list = [set()]                      # object -> set of sources
        self.live = 1
        self.points: frozenset = frozenset()
        self.composed: dict = {}
        self.small: list = [[] for _ in range(CAP)]   # bucket queue of eliminate(), empty between calls
        self.stats = {"max_objects_before_elimination": 0, "max_objects_after_elimination": 0,
                      "eliminations": 0, "max_boundary": 0, "compositions": 0}

    def _check(self) -> None:
        if self.deadline is not None and monotonic() > self.deadline:
            raise ScanLimit("time budget exhausted")

    def _intern(self, matching) -> int:
        ident = self.ids.get(matching)
        if ident is None:
            ident = self.ids[matching] = len(self.matchings)
            self.matchings.append(matching)
        return ident

    # ----- one crossing --------------------------------------------------
    def add_crossing(self, slots: tuple, reduce_now: bool = True) -> None:
        self._check()
        alg, matchings, points = self.algebra, self.matchings, self.points
        alg.clear()
        self.composed = {}
        old_mid, old_deg, old_out = self.mid, self.deg, self.out
        glued: dict = {}
        count = 0
        new_points = None
        for ma in set(old_mid):
            if ma is None:
                continue
            g0 = alg.gluing(matchings[ma], 0, points, slots)
            g1 = alg.gluing(matchings[ma], 1, points, slots)
            glued[ma] = (self._intern(g0.matching), 1 << g0.closed, self._intern(g1.matching), 1 << g1.closed)
            new_points = g0.points
        if self.max_objects is not None:
            count = sum(glued[ma][1] + glued[ma][3] for ma in old_mid if ma is not None)
            if count > self.max_objects:
                raise ScanLimit(f"{count} objects would exceed the ceiling {self.max_objects}")
        mid: list = []
        deg: list = []
        base = [None] * len(old_mid)
        for o, ma in enumerate(old_mid):
            if ma is None:
                continue
            nm0, k0, nm1, k1 = glued[ma]
            b0 = len(mid)
            base[o] = (b0, b0 + k0)
            h = old_deg[o]
            mid += [nm0] * k0 + [nm1] * k1
            deg += [h] * k0 + [h + 1] * k1
        total = len(mid)
        out = [{} for _ in range(total)]
        inc = [set() for _ in range(total)]
        saddles: dict = {}
        transfers: dict = {}
        for o, ma in enumerate(old_mid):
            if ma is None:
                continue
            b0, b1 = base[o]
            entries = saddles.get(ma)
            if entries is None:
                m = matchings[ma]
                entries = saddles[ma] = self._pack(alg.crossing_entries(m, m, 1, 0, 1, points, slots)[2])
            for ls, lt, value in entries:
                out[b0 + ls][b1 + lt] = value
                inc[b1 + lt].add(b0 + ls)
            for o2, f in old_out[o].items():
                key = (ma, old_mid[o2], f)
                both = transfers.get(key)
                if both is None:
                    m, m2 = matchings[ma], matchings[key[1]]
                    both = transfers[key] = (
                        self._pack(alg.crossing_entries(m, m2, f, 0, 0, points, slots)[2]),
                        self._pack(alg.crossing_entries(m, m2, f, 1, 1, points, slots)[2]))
                c0, c1 = base[o2]
                for ls, lt, value in both[0]:
                    out[b0 + ls][c0 + lt] = value
                    inc[c0 + lt].add(b0 + ls)
                for ls, lt, value in both[1]:
                    out[b1 + ls][c1 + lt] = value
                    inc[c1 + lt].add(b1 + ls)
        self.mid, self.deg, self.out, self.inc, self.live = mid, deg, out, inc, total
        if new_points is None:
            new_points = glue_points(points, slots)
        self.points = new_points
        stats = self.stats
        if total > stats["max_objects_before_elimination"]:
            stats["max_objects_before_elimination"] = total
        if len(new_points) > stats["max_boundary"]:
            stats["max_boundary"] = len(new_points)
        if reduce_now:
            self.eliminate()
            if self.live > stats["max_objects_after_elimination"]:
                stats["max_objects_after_elimination"] = self.live

    @staticmethod
    def _pack(entries) -> tuple:
        """Delooping labels as offsets inside the block of an old object."""
        return tuple((sum(bit << j for j, bit in enumerate(ls)), sum(bit << j for j, bit in enumerate(lt)), value)
                     for ls, lt, value in entries)

    # ----- composition -----------------------------------------------------
    def _compose(self, key) -> int:
        """Cache miss of g o f; key = (id a, id b, id c, f, g)."""
        a, b, c, f, g = key
        matchings = self.matchings
        plan = self.algebra.plan(matchings[a], matchings[b], matchings[c])
        result = 0
        if plan is not None:
            for tf in bits(f):
                for tg in bits(g):
                    result ^= evaluate(plan, tf, tg)
        self.composed[key] = result
        return result

    # ----- Gaussian elimination -------------------------------------------
    def eliminate(self) -> None:
        """Cancel unit entries between equal matchings, cheapest (Markowitz) first."""
        mid, out, inc, composed = self.mid, self.out, self.inc, self.composed
        miss = self._compose
        # Bucket queue: most Markowitz costs are tiny, and most candidates die
        # unused when a neighbour is cancelled, so a list per small cost (plus a
        # heap for the rare large costs) beats one big heap.  (Queuing only the
        # cheapest candidate of each source was tried: fewer queue operations,
        # but 45% more compositions from worse pivots.)
        small, large = self.small, []
        for a, row in enumerate(out):
            if row:
                ma = mid[a]
                width = len(row) - 1
                for b, f in row.items():
                    if f & 1 and mid[b] == ma:
                        cost = width * (len(inc[b]) - 1)
                        if cost < CAP:
                            small[cost].append((a, b))
                        else:
                            large.append((cost, a, b))
        heapify(large)
        lo = 0
        eliminations = compositions = 0
        deadline = self.deadline
        while True:
            while lo < CAP and not small[lo]:
                lo += 1
            if lo < CAP:
                cost = lo
                b, c = small[lo].pop()
            elif large:
                cost, b, c = heappop(large)
            else:
                break
            rowb = out[b]
            if rowb is None:
                continue
            phi = rowb.get(c)
            if phi is None or not phi & 1:
                continue
            incc = inc[c]
            actual = (len(rowb) - 1) * (len(incc) - 1)
            if actual > cost:                         # stale priority: file it again
                if actual < CAP:
                    small[actual].append((b, c))
                else:
                    heappush(large, (actual, b, c))
                continue
            eliminations += 1
            if deadline is not None and not eliminations & 255:
                self._check()
            m = mid[b]
            # detach b and c from the complex
            del rowb[c]
            incc.discard(b)
            ins = [(a, out[a].pop(c)) for a in incc]
            for y in rowb:
                inc[y].discard(b)
            for y in inc[b]:
                del out[y][b]
            for y in out[c]:
                inc[y].discard(c)
            out[b] = out[c] = inc[b] = inc[c] = mid[b] = mid[c] = None
            if not rowb:
                continue
            outs = [(f, gamma, mid[f]) for f, gamma in rowb.items()]
            for a, delta in ins:
                ma = mid[a]
                if phi == 1:
                    half = delta
                else:
                    compositions += 1
                    key = (ma, m, m, delta, phi)
                    half = composed.get(key)
                    if half is None:
                        half = miss(key)
                    if not half:
                        continue
                rowa = out[a]
                same = ma == m
                for f, gamma, mf in outs:
                    if half == 1 and same:
                        term = gamma
                    elif gamma == 1 and mf == m:
                        term = half
                    else:
                        compositions += 1
                        key = (ma, m, mf, half, gamma)
                        term = composed.get(key)
                        if term is None:
                            term = miss(key)
                        if not term:
                            continue
                    current = rowa.get(f, 0) ^ term
                    if current:
                        rowa[f] = current
                        inc[f].add(a)
                        if current & 1 and ma == mf:
                            cost = (len(rowa) - 1) * (len(inc[f]) - 1)
                            if cost < CAP:
                                small[cost].append((a, f))
                                if cost < lo:
                                    lo = cost
                            else:
                                heappush(large, (cost, a, f))
                    else:
                        del rowa[f]
                        inc[f].discard(a)
        self.live -= 2 * eliminations
        self.stats["eliminations"] += eliminations
        self.stats["compositions"] += compositions

    # ----- closing ---------------------------------------------------------
    def linear_ranks(self) -> dict[int, int]:
        """Homology dimensions of the closed complex by F2 linear algebra (``tail`` mode)."""
        if self.points:
            raise ValueError("the diagram is not closed yet")
        by_degree: dict[int, list[int]] = defaultdict(list)
        for ident, ma in enumerate(self.mid):
            if ma is not None:
                by_degree[self.deg[ident]].append(ident)
        rank: dict[int, int] = {}
        for h, sources in by_degree.items():
            index = {ident: k for k, ident in enumerate(by_degree.get(h + 1, []))}
            pivots: dict[int, int] = {}
            for a in sources:
                self._check()
                column = 0
                for b, value in self.out[a].items():
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
        if any(self.out):
            raise ArithmeticError("minimal closed complex still has a nonzero differential")
        return self.live

    def ranks_by_degree(self) -> dict[int, int]:
        counts: dict[int, int] = defaultdict(int)
        for ident, ma in enumerate(self.mid):
            if ma is not None:
                counts[self.deg[ident]] += 1
        return dict(sorted(counts.items()))

    def check_d_squared(self) -> None:
        alg, matchings, mid, out = self.algebra, self.matchings, self.mid, self.out
        for a, row in enumerate(out):
            if not row:
                continue
            acc: dict = {}
            ma = matchings[mid[a]]
            for b, f in row.items():
                mb = matchings[mid[b]]
                for c, g in out[b].items():
                    acc[c] = acc.get(c, 0) ^ alg.compose(f, g, ma, mb, matchings[mid[c]])
            for c, value in acc.items():
                if value:
                    raise ArithmeticError(f"d^2 != 0 between objects {a} and {c}")


def glue_points(points: frozenset, slots: tuple) -> frozenset:
    """Boundary labels after attaching a crossing (used only when the complex is empty)."""
    once = {label for label in slots if slots.count(label) == 1}
    return frozenset((points - once) | (once - points))
