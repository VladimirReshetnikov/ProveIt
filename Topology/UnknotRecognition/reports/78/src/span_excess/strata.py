"""Canonical sparse positive-defect enumeration; no height-level expansion."""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations, product
from math import comb
from .model import HeightModel, Constraint, integer, noop


@dataclass(frozen=True)
class Stratum:
    # (slot, positive defect, realizing corner), increasing slot order.
    # Slot 2*t is an upper defect; slot 2*t+1 is a lower defect.
    entries: tuple[tuple[int, int, int], ...] = ()

    @property
    def excess(self) -> int:
        return sum(d for _, d, _ in self.entries)

    def to_list(self) -> list[list[int]]:
        return [list(x) for x in self.entries]


def stratum_count(t: int, k: int) -> int:
    if integer(t) < 1 or integer(k) < 0:
        raise ValueError("T >= 1 and k >= 0 required")
    return sum(comb(2*t, j) * 3**j * comb(k, j)
               for j in range(min(2*t, k) + 1))


def _positive_compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for first in range(1, total - parts + 2):
        for tail in _positive_compositions(total-first, parts-1):
            yield (first,) + tail


def enumerate_strata(model: HeightModel, k: int, check=noop):
    if integer(k) < 0:
        raise ValueError("negative excess")
    yield Stratum()
    slots = 2 * len(model.vertices)
    for total in range(1, k+1):
        for j in range(1, min(slots, total)+1):
            for support in combinations(range(slots), j):
                check()
                corners = []
                for s in support:
                    anchor = model.high[s//2] if s % 2 == 0 else model.low[s//2]
                    corners.append(tuple(i for i in range(4) if i != anchor))
                for values in _positive_compositions(total, j):
                    for witnesses in product(*corners):
                        check()
                        yield Stratum(tuple(zip(support, values, witnesses)))


def constraints_for(model: HeightModel, cell: Stratum) -> tuple[Constraint, ...]:
    slots = 2*len(model.vertices)
    sparse = {}
    previous = -1
    for s, d, witness in cell.entries:
        if not previous < integer(s) < slots or integer(d) < 1:
            raise ValueError("invalid positive-defect support")
        if not 0 <= integer(witness) < 4:
            raise ValueError("invalid realizing corner")
        previous = s
        anchor = model.high[s//2] if s % 2 == 0 else model.low[s//2]
        if witness == anchor:
            raise ValueError("positive defect cannot be realized by its anchor")
        sparse[s] = (d, witness)
    arcs = []
    for t, (vs, hs, lo, hi) in enumerate(zip(model.vertices, model.heights,
                                             model.low, model.high)):
        upper, uw = sparse.get(2*t, (0, hi))
        lower, lw = sparse.get(2*t+1, (0, lo))
        for i in range(4):
            # a_i-a_hi <= upper; a_lo-a_i <= lower.
            arcs.append((vs[hi], vs[i], hs[hi]-hs[i]+upper))
            arcs.append((vs[i], vs[lo], hs[i]-hs[lo]+lower))
        if upper:
            # Reverse inequality certifies equality at uw.
            arcs.append((vs[uw], vs[hi], hs[uw]-hs[hi]-upper))
        if lower:
            arcs.append((vs[lo], vs[lw], hs[lo]-hs[lw]-lower))
    return tuple(arcs)


def containing_stratum(model: HeightModel, p) -> Stratum:
    entries = []
    for t, (a, lo, hi) in enumerate(zip(model.adjusted(p), model.low, model.high)):
        dp, dm = max(a)-a[hi], a[lo]-min(a)
        if dp:
            entries.append((2*t, dp, a.index(max(a))))
        if dm:
            entries.append((2*t+1, dm, a.index(min(a))))
    return Stratum(tuple(entries))
