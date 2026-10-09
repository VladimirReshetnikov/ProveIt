"""Source-anchored, normalization-free primitive-pair contraction.

This module is an algebraic kernel, NOT an unknot-verdict API. Proper-power
steps require independently established torsion-freeness of the source group.
The returned proof records that obligation rather than accepting a caller flag.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from math import gcd
from typing import Callable
from .grammar import Source, ResourceLimit


def encode_int(x: int) -> str:
    return hex(x)


@dataclass(frozen=True)
class Witness:
    slot: int
    a: int
    b: int
    u: int
    v: int
    exponent: int
    width: int

    def payload(self) -> dict:
        return {'slot': self.slot, 'pair': [self.a, self.b],
                'vector': [encode_int(self.u), encode_int(self.v)],
                'exponent': encode_int(self.exponent), 'width': encode_int(self.width)}


@dataclass
class AnchoredState:
    source: Source
    max_work: int | None = None
    cancel: Callable[[], bool] | None = None
    images: dict[int, tuple[int, int]] = field(init=False)
    alive: set[int] = field(init=False)
    dead: set[int] = field(default_factory=set)
    steps: list[list[Witness]] = field(default_factory=list)
    work: int = 0

    def __post_init__(self) -> None:
        self.images = {g: (g, 1) for g in self.source.generators}
        self.alive = set(self.source.generators)

    def tick(self, amount: int = 1) -> None:
        self.work += amount
        if self.max_work is not None and self.work > self.max_work:
            raise ResourceLimit("cooperative work limit")
        if self.cancel is not None and self.cancel():
            raise ResourceLimit("cancelled")

    def summaries(self) -> list[dict[int, tuple[int, int]] | None]:
        """Capped signed occurrence counts; recomputed for every image table."""
        vals: list[dict[int, tuple[int, int]] | None] = [{}]
        for rule in self.source.rules[1:]:
            self.tick()
            if rule[0] == 't':
                x = rule[1]
                g, k = self.images[abs(x)]
                positive = (x > 0) == (k > 0)
                vals.append({g: (abs(k), 0) if positive else (0, abs(k))})
                continue
            left, right = vals[rule[1]], vals[rule[2]]
            if left is None or right is None or len(left.keys() | right.keys()) > 2:
                vals.append(None)
                continue
            merged = dict(left)
            for g, (p, n) in right.items():
                a, b = merged.get(g, (0, 0))
                merged[g] = a + p, b + n
            vals.append(merged)
        return vals

    def width(self, root: int, a: int, b: int, p: int, q: int) -> int:
        """Height increments +q on a and -p on b; signs handled by coherence."""
        vals = [(0, 0, 0)]
        for rule in self.source.rules[1:]:
            self.tick()
            if rule[0] == 't':
                g, k = self.images[abs(rule[1])]
                delta = abs(k) * (q if g == a else -p if g == b else 0)
                vals.append((delta, min(0, delta), max(0, delta)))
            else:
                d, lo, hi = vals[rule[1]]
                e, low, high = vals[rule[2]]
                vals.append((d + e, min(lo, d + low), max(hi, d + high)))
        delta, low, high = vals[root]
        if delta:
            raise AssertionError("non-closed profile after occurrence check")
        return high - low

    def plan(self, max_pairs: int | None = None) -> list[Witness]:
        if max_pairs is not None and (type(max_pairs) is not int or max_pairs < 1):
            raise ValueError("max_pairs must be positive")
        summaries = self.summaries()
        selected: list[Witness] = []
        used: set[int] = set()
        for slot, root in enumerate(self.source.roots):
            self.tick()
            if slot in self.dead:
                continue
            counts = summaries[root]
            if counts is None or len(counts) != 2 or any(p and n for p, n in counts.values()):
                continue
            a, b = sorted(counts)
            if a in used or b in used:
                continue
            ua = counts[a][0] - counts[a][1]
            vb = counts[b][0] - counts[b][1]
            exponent = gcd(abs(ua), abs(vb))
            u, v = ua // exponent, vb // exponent
            wanted = abs(u) + abs(v) - 1
            width = wanted if min(abs(ua), abs(vb)) == 1 else self.width(root, a, b, abs(u), abs(v))
            if width != wanted:
                continue
            selected.append(Witness(slot, a, b, u, v, exponent, width))
            used.update((a, b))
            if max_pairs is not None and len(selected) >= max_pairs:
                break
        return selected

    def apply_planned(self, selected: list[Witness]) -> None:
        """Internal producer operation; independent verification is in verify.py."""
        if not selected:
            raise ValueError("empty batch")
        local: dict[int, tuple[int, int]] = {}
        used_slots = set()
        for w in selected:
            if (w.a not in self.alive or w.b not in self.alive or w.a >= w.b or
                    w.a in local or w.b in local or w.slot in self.dead or
                    w.slot in used_slots or not w.u or not w.v or gcd(abs(w.u), abs(w.v)) != 1):
                raise ValueError("invalid internal disjoint batch")
            used_slots.add(w.slot)
            sign = 1 if w.v > 0 else -1
            local[w.a] = (w.a, abs(w.v))
            local[w.b] = (w.a, -w.u * sign)
        images = {}
        for original, (g, k) in self.images.items():
            self.tick()
            target, factor = local.get(g, (g, 1))
            images[original] = target, k * factor
        self.images = images
        self.alive.difference_update(w.b for w in selected)
        self.dead.update(used_slots)
        self.steps.append(list(selected))

    def rank_one_zero(self) -> bool:
        if len(self.alive) != 1:
            return False
        vals = [0]
        for rule in self.source.rules[1:]:
            self.tick()
            if rule[0] == 't':
                x = rule[1]
                k = self.images[abs(x)][1]
                vals.append(k if x > 0 else -k)
            else:
                vals.append(vals[rule[1]] + vals[rule[2]])
        return all(slot in self.dead or vals[root] == 0
                   for slot, root in enumerate(self.source.roots))

    def run(self, max_pairs: int | None = None) -> dict:
        while len(self.alive) > 1:
            batch = self.plan(max_pairs)
            if not batch:
                break
            self.apply_planned(batch)
        endpoint = ('rank_one_zero' if self.rank_one_zero() else
                    'rank_one_nonzero' if len(self.alive) == 1 else 'stalled')
        return {'format': 'source-anchored-projection-v1', 'source_sha256': self.source.digest,
                'steps': [[w.payload() for w in batch] for batch in self.steps],
                'endpoint': endpoint}
