"""Exact rooted disc-component features. No manifold or knot verdicts.

Coordinates are (ternary word on labels 1..r-1, charge in F_2^k).
A bad block is a connected non-disc surface, under the arc-only contract.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Iterable
import hashlib
import json


class ResourceLimit(RuntimeError):
    """The computation is incomplete; never interpret this as nonexistence."""


def _integer(x: object) -> bool:
    return type(x) is int


@dataclass(frozen=True)
class State:
    partition: tuple[int, ...]
    good: tuple[bool, ...]
    charges: tuple[int, ...]
    q: int = 1

    def __post_init__(self) -> None:
        if not isinstance(self.partition, tuple) or not self.partition:
            raise ValueError("a state has a nonempty tuple of labels, including root 0")
        if not _integer(self.q) or self.q < 1 or self.q & (self.q - 1):
            raise ValueError("q must be a positive power of two")
        high = -1
        for b in self.partition:
            if not _integer(b) or not 0 <= b <= high + 1:
                raise ValueError("partition must be a restricted-growth string")
            high = max(high, b)
        k = high + 1
        if not isinstance(self.good, tuple) or len(self.good) != k or any(type(g) is not bool for g in self.good):
            raise ValueError("one Boolean disk flag per block is required")
        if not isinstance(self.charges, tuple) or len(self.charges) != k:
            raise ValueError("one charge per block is required")
        if any(not _integer(h) or not 0 <= h < self.q for h in self.charges):
            raise ValueError("charge is outside F_2^k")
        if any(h and not g for h, g in zip(self.charges, self.good)):
            raise ValueError("bad-block charges must be canonically zero")

    @property
    def r(self) -> int:
        return len(self.partition)

    def as_dict(self) -> dict:
        return {"partition": list(self.partition), "good": list(self.good),
                "charges": list(self.charges), "q": self.q}

    @classmethod
    def from_dict(cls, d: dict) -> State:
        if set(d) != {"partition", "good", "charges", "q"}:
            raise ValueError("unexpected state fields")
        return cls(tuple(d["partition"]), tuple(d["good"]), tuple(d["charges"]), d["q"])


def partitions(n: int) -> Iterable[tuple[int, ...]]:
    if not _integer(n) or n < 1:
        raise ValueError("n must be positive")
    def visit(p: tuple[int, ...]):
        if len(p) == n:
            yield p
        else:
            for x in range(max(p) + 2):
                yield from visit(p + (x,))
    yield from visit((0,))


def decorated_states(r: int, q: int = 1, root_good: bool = True) -> Iterable[State]:
    """Enumerate only for small audits, never required by the search algorithm."""
    for p in partitions(r):
        k = max(p) + 1
        choices = [None] + list(range(q))  # None = bad, integers = good charge
        for flags in product(choices, repeat=k - 1):
            for root in (list(range(q)) if root_good else choices):
                a = (root,) + flags
                yield State(p, tuple(v is not None for v in a),
                            tuple(0 if v is None else v for v in a), q)


@lru_cache(maxsize=4096)
def feature(s: State, max_dimension: int = 2_000_000) -> int:
    """Packed binary feature; construct its support block-by-block, not by Bell enumeration."""
    dimension = s.q * 3 ** (s.r - 1)
    if dimension > max_dimension:
        raise ResourceLimit(f"feature dimension {dimension} exceeds {max_dimension}")
    if not s.good[0]:
        return 0
    powers = [0] + [3 ** (i - 1) for i in range(1, s.r)]
    blocks = [[] for _ in s.good]
    for i, b in enumerate(s.partition):
        blocks[b].append(i)
    root_code = sum(powers[i] for i in blocks[0])
    entries = [(root_code, s.charges[0])]
    for b in range(1, len(blocks)):
        if not s.good[b]:
            continue  # every point in a bad block stays outside X
        all_one = sum(powers[i] for i in blocks[b])
        old = entries
        entries = old.copy()  # omit this whole block
        for code, charge in old:
            for representative in blocks[b]:
                entries.append((code + all_one + powers[representative], charge ^ s.charges[b]))
    row = 0
    for code, charge in entries:
        row |= 1 << (code * s.q + charge)
    return row


@lru_cache(maxsize=64)
def transpose_codes(r: int) -> tuple[int, ...]:
    """Swap ternary digits 1 and 2, fixing 0."""
    ans = []
    for code in range(3 ** (r - 1)):
        x, out, power = code, 0, 1
        for _ in range(r - 1):
            digit = x % 3
            out += (0 if digit == 0 else 3 - digit) * power
            x //= 3
            power *= 3
        ans.append(out)
    return tuple(ans)


def dual_row(s: State, target: int | None = 0) -> int:
    """Dual row for exact charge target, or any nonzero charge when target=None."""
    if target is not None and (not _integer(target) or not 0 <= target < s.q):
        raise ValueError("invalid target")
    raw, out = feature(s), 0
    codes = transpose_codes(s.r)
    while raw:
        bit = raw & -raw
        j = bit.bit_length() - 1
        code, charge = divmod(j, s.q)
        allowed = (charge ^ target,) if target is not None else (h for h in range(s.q) if h != charge)
        for h in allowed:
            out ^= 1 << (codes[code] * s.q + h)
        raw ^= bit
    return out


def pairing(s: State, t: State, target: int | None = 0) -> bool:
    if s.r != t.r or s.q != t.q:
        raise ValueError("incompatible interfaces")
    return bool((feature(s) & dual_row(t, target)).bit_count() & 1)


def direct_compatibility(s: State, t: State, target: int | None = 0) -> bool:
    """Independent graph definition, with BFS and edge/vertex counting, no features."""
    if s.r != t.r or s.q != t.q:
        raise ValueError("incompatible interfaces")
    if target is not None and (not _integer(target) or not 0 <= target < s.q):
        raise ValueError("invalid target")
    offset = len(s.good)
    n = offset + len(t.good)
    adj = [[] for _ in range(n)]
    for a, b in zip(s.partition, t.partition):
        adj[a].append(offset + b)
        adj[offset + b].append(a)
    seen, todo = {0}, [0]
    while todo:
        v = todo.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                todo.append(w)
    flags = s.good + t.good
    if any(not flags[v] for v in seen):
        return False
    if sum(len(adj[v]) for v in seen) // 2 != len(seen) - 1:
        return False
    h = 0
    labels = s.charges + t.charges
    for v in seen:
        h ^= labels[v]
    return (h != 0) if target is None else (h == target)


@dataclass(frozen=True)
class Candidate:
    state: State
    cost: int
    witness: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.state, State) or not _integer(self.cost):
            raise ValueError("candidate needs a State and an integer cost")
        if not isinstance(self.witness, tuple) or any(not _integer(x) for x in self.witness):
            raise ValueError("witness must be an integer tuple")

    def as_dict(self) -> dict:
        return {"state": self.state.as_dict(), "cost": hex(self.cost), "witness": list(self.witness)}


def source_digest(candidates: list[Candidate], geometry_key: str) -> str:
    blob = {"geometry_key": geometry_key, "candidates": [c.as_dict() for c in candidates]}
    return hashlib.sha256(json.dumps(blob, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def reduce_candidates(candidates: Iterable[Candidate], *, geometry_key: str = "abstract",
                      certificate: bool = True, max_dimension: int = 2_000_000) -> tuple[list[Candidate], dict | None]:
    """Cost-ordered original-witness basis. The caller supplies one common geometry key."""
    candidates = list(candidates)
    if not isinstance(geometry_key, str):
        raise ValueError("geometry key must be a string")
    if candidates and any((c.state.r, c.state.q) != (candidates[0].state.r, candidates[0].state.q) for c in candidates):
        raise ValueError("mixed interfaces")
    pivots: dict[int, tuple[int, int]] = {}
    kept: list[int] = []
    expressions = [0] * len(candidates)
    for idx in sorted(range(len(candidates)), key=lambda i: (candidates[i].cost, i)):
        row = feature(candidates[idx].state, max_dimension)
        combination = 0
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                slot = len(kept)
                kept.append(idx)
                pivots[p] = (row, combination ^ (1 << slot))
                expressions[idx] = 1 << slot
                break
            reduced, expression = pivots[p]
            row ^= reduced
            combination ^= expression
        else:
            expressions[idx] = combination
    cert = None
    if certificate:
        cert = {"format": "rooted-disc-basis-v1", "geometry_key": geometry_key,
                "source_sha256": source_digest(candidates, geometry_key), "kept": kept,
                "expressions_hex": [hex(x) for x in expressions]}
    return [candidates[i] for i in kept], cert


def binary_rank(rows: Iterable[int]) -> int:
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row
                break
            row ^= pivots[p]
    return len(pivots)


def star_states(r: int, q: int = 1) -> Iterable[tuple[State, int, tuple[str, ...]]]:
    """Tensor lower-bound family, with costs exposing every exact-charge witness."""
    for word in product(("R", "G", "B"), repeat=r - 1):
        p, good, charges = [0], [True], [0]
        for c in word:
            if c == "R":
                p.append(0)
            else:
                p.append(len(good)); good.append(c == "G"); charges.append(0)
        cost = sum({"R": 0, "B": 1, "G": 2}[c] for c in word)
        for h in range(q):
            charges[0] = h
            yield State(tuple(p), tuple(good), tuple(charges), q), cost, word
