#!/usr/bin/env python3
"""Exact certificates for the reverse-reply theorem.

Python 3.10+; standard library only. All permutations are ONE-BASED.
No exhaustive search or computation is an assumption in the mathematical proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from bisect import bisect_left
from itertools import combinations
from typing import Iterable, Sequence

Perm = tuple[int, ...]


def standardize(values: Sequence[int]) -> Perm:
    """Replace distinct values by their ranks, starting at one."""
    if len(set(values)) != len(values):
        raise ValueError("Entries must be distinct")
    ranks = {v: i + 1 for i, v in enumerate(sorted(values))}
    return tuple(ranks[v] for v in values)


def validate(p: Sequence[int]) -> Perm:
    p = tuple(p)
    if sorted(p) != list(range(1, len(p) + 1)):
        raise ValueError("Expected a one-based permutation")
    return p


def monotone(p: Perm) -> bool:
    return p == tuple(range(1, len(p) + 1)) or p == tuple(range(len(p), 0, -1))


def bound(k: int) -> int:
    if k < 3:
        raise ValueError("The stated general bound is for k >= 3")
    return k + (k + 1) ** 2 * (k - 2) ** 2 + 1


def shadow_direct(p: Sequence[int], k: int) -> frozenset[Perm]:
    """Independent direct enumeration of all k-subsequences."""
    if k < 1:
        raise ValueError("k must be positive")
    return frozenset(standardize(tuple(p[i] for i in ix))
                     for ix in combinations(range(len(p)), k))


@dataclass(frozen=True)
class Template:
    """Inflate beta[index] monotonically; every other entry stays singleton."""
    beta: Perm
    index: int
    sign: int

    def __post_init__(self) -> None:
        validate(self.beta)
        if not 0 <= self.index < len(self.beta):
            raise ValueError("Invalid marked index")
        if self.sign not in (-1, 1):
            raise ValueError("Block sign must be +1 or -1")

    @property
    def singletons(self) -> int:
        return len(self.beta) - 1

    def inflate(self, t: int) -> Perm:
        if t < 1:
            raise ValueError("Block length must be positive")
        v = self.beta[self.index]
        out: list[int] = []
        for i, x in enumerate(self.beta):
            if i == self.index:
                block = list(range(v, v + t))
                out.extend(block if self.sign == 1 else reversed(block))
            else:
                out.append(x if x < v else x + t - 1)
        return tuple(out)

    def delete(self, index: int) -> Template:
        if index == self.index or not 0 <= index < len(self.beta):
            raise ValueError("Delete a singleton, not the marked entry")
        vals = self.beta[:index] + self.beta[index + 1:]
        return Template(standardize(vals), self.index - (index < self.index), self.sign)

    def stable_shadow(self, k: int, *, nonmonotone: bool = True) -> frozenset[Perm]:
        """Symbolic shadow, independent of direct subsequence enumeration.

        Enumerate the chosen singleton indices and the NUMBER of block entries.
        Full shadows stabilize at t=k, nonmonotone shadows at t=k-1.
        """
        if k < 2:
            raise ValueError("Use k >= 2")
        ordinary = tuple(i for i in range(len(self.beta)) if i != self.index)
        out: set[Perm] = set()
        for a in range(min(k, len(ordinary)) + 1):
            b = k - a
            for chosen in combinations(ordinary, a):
                if b == 0:
                    q = standardize(tuple(self.beta[i] for i in chosen))
                else:
                    ix = sorted(chosen + (self.index,))
                    reduced = Template(standardize(tuple(self.beta[i] for i in ix)),
                                       ix.index(self.index), self.sign)
                    q = reduced.inflate(b)
                if not nonmonotone or not monotone(q):
                    out.add(q)
        return frozenset(out)

    def record(self) -> dict:
        return {"beta": list(self.beta), "marked_index_zero_based": self.index,
                "sign": self.sign, "singletons": self.singletons}


def isolate(template: Template, targets: Iterable[Perm]) -> tuple[Template, list[dict]]:
    """Greedily minimize singleton support, retaining some target occurrence."""
    Q = frozenset(validate(q) for q in targets)
    if not Q:
        raise ValueError("At least one target is required")
    k = len(next(iter(Q)))
    if any(len(q) != k or monotone(q) for q in Q):
        raise ValueError("Targets must be nonmonotone with a common length")
    if not template.stable_shadow(k) & Q:
        raise ValueError("The template contains no target")
    trace = [template.record()]
    while True:
        for j in range(len(template.beta)):
            if j == template.index:
                continue
            candidate = template.delete(j)
            if candidate.stable_shadow(k) & Q:
                template = candidate
                trace.append(template.record())
                break
        else:
            break
    assert len(template.stable_shadow(k) & Q) == 1
    return template, trace


def monotone_indices(values: Sequence[int], h: int) -> tuple[tuple[int, ...], int]:
    """O(N^2) integer-only ES witness; returns indices and sign."""
    if h < 1:
        raise ValueError("h must be positive")
    n = len(values)
    lengths = [[1] * n, [1] * n]
    parents = [[-1] * n, [-1] * n]
    for j in range(n):
        for i in range(j):
            mode = 0 if values[i] < values[j] else 1
            if lengths[mode][i] + 1 > lengths[mode][j]:
                lengths[mode][j] = lengths[mode][i] + 1
                parents[mode][j] = i
        for mode in (0, 1):
            if lengths[mode][j] >= h:
                path = []
                pos = j
                for _ in range(h):
                    path.append(pos)
                    pos = parents[mode][pos]
                return tuple(reversed(path)), (1 if mode == 0 else -1)
    raise ValueError("No monotone subsequence of the requested length")


def extract(pi: Perm, occurrence: Sequence[int], k: int) -> tuple[Template, dict]:
    """Extract k singletons plus a same-cell monotone block of length k-1."""
    pi = validate(pi)
    occ = tuple(occurrence)
    if len(occ) != k or tuple(sorted(set(occ))) != occ:
        raise ValueError("Occurrence must contain k increasing distinct indices")
    if not occ or occ[0] < 0 or occ[-1] >= len(pi):
        raise ValueError("Occurrence index outside permutation")
    if len(pi) < bound(k):
        raise ValueError("This certified extraction requires n >= B(k)")
    values = sorted(pi[i] for i in occ)
    marked = set(occ)
    cells: dict[tuple[int, int], list[int]] = {}
    for i, v in enumerate(pi):
        if i not in marked:
            cell = (bisect_left(occ, i), bisect_left(values, v))
            cells.setdefault(cell, []).append(i)
    cell, indices = max(cells.items(), key=lambda item: len(item[1]))
    h = k - 1
    assert len(indices) >= (h - 1) ** 2 + 1
    local, sign = monotone_indices([pi[i] for i in indices], h)
    block = tuple(indices[i] for i in local)
    # One block representative has the same gap position and value as all others.
    skeleton_indices = sorted(occ + (block[0],))
    template = Template(standardize(tuple(pi[i] for i in skeleton_indices)),
                        skeleton_indices.index(block[0]), sign)
    selected = sorted(occ + block)
    assert template.inflate(h) == standardize(tuple(pi[i] for i in selected))
    return template, {"occurrence_zero_based": list(occ), "cell": list(cell),
                      "cell_size": len(indices), "block_indices_zero_based": list(block),
                      "template": template.record()}


def construct_reply(pi: Perm, p: Perm, occurrence: Sequence[int],
                    forbidden: Iterable[Perm] = ()) -> tuple[Perm, dict]:
    """Construct a length-n p^r witness after forbidding p.

    A marked occurrence is supplied to avoid an n-choose-k occurrence search.
    The finite extracted template is checked against F directly. In particular,
    output validity does not rely on an unverified exhaustive test on pi.
    """
    pi, p = validate(pi), validate(p)
    k, n = len(p), len(pi)
    F = frozenset(validate(f) for f in forbidden)
    if monotone(p) or any(len(f) != k or monotone(f) for f in F):
        raise ValueError("Use nonmonotone patterns of length k")
    if any(f[::-1] not in F for f in F):
        raise ValueError("F must be reversal-closed")
    if p in F:
        raise ValueError("The proposed first move is already forbidden")
    if standardize(tuple(pi[i] for i in occurrence)) != p:
        raise ValueError("Marked indices do not form the requested pattern")
    original, extraction = extract(pi, occurrence, k)
    if original.stable_shadow(k) & F:
        raise ValueError("The extracted witness contains a forbidden pattern")
    minimal, trace = isolate(original, (p, p[::-1]))
    sh = minimal.stable_shadow(k)
    reverse = p in sh
    assert ((p in sh) != (p[::-1] in sh))
    t = n - minimal.singletons
    reply = minimal.inflate(t)
    if reverse:
        reply = reply[::-1]
    output_shadow = frozenset(q[::-1] for q in sh) if reverse else sh
    assert p not in output_shadow and p[::-1] in output_shadow
    assert not (output_shadow & F)
    return reply, {"k": k, "n": n, "bound": bound(k), "p": list(p),
                   "forbidden": [list(f) for f in sorted(F)],
                   "extraction": extraction, "deletion_trace": trace,
                   "minimal_template": minimal.record(), "output_block_length": t,
                   "reverse_output": reverse,
                   "stable_nonmonotone_shadow": [list(q) for q in sorted(output_shadow)]}
