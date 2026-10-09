"""Weighted disc-completion representatives over F_2.

This is a relation-level research kernel, NOT an unknot recognizer.
Partitions describe individually labelled, whole boundary intervals. They do
not authenticate embeddings, normal admissibility, or compressed multiplicities.
The checker in check_certificate.py deliberately does not import this module.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from itertools import product
import json
from math import comb
from typing import Iterable


class ResourceLimit(RuntimeError):
    """An explicit resource cap was reached; no topology verdict is implied."""


@dataclass(frozen=True)
class Candidate:
    id: str
    partition: tuple[int, ...]
    cost: int = 0
    control: str = "default"

    def record(self) -> dict:
        # Hexadecimal costs avoid decimal conversion limits for huge integers.
        return {"id": self.id, "partition": list(self.partition),
                "cost_hex": hex(self.cost), "control": self.control}


def validate_partition(p: tuple[int, ...], r: int | None = None) -> None:
    if not isinstance(p, tuple) or not p or (r is not None and len(p) != r):
        raise ValueError("partition must be a nonempty tuple of the specified length")
    hi = -1
    for v in p:
        if type(v) is not int or v < 0 or v > hi + 1:
            raise ValueError("partition is not a canonical restricted-growth string")
        hi = max(hi, v)


def grade(p: tuple[int, ...]) -> int:
    return len(p) - max(p) - 1


def blocks(p: tuple[int, ...]) -> list[list[int]]:
    result: list[list[int]] = [[] for _ in range(max(p) + 1)]
    for i, b in enumerate(p):
        result[b].append(i)
    return result


def exterior_feature(p: tuple[int, ...]) -> int:
    """Rooted-transversal coordinates; bit I is the exterior coefficient e_I.

    The ambient bit vector has 2**(r-1) positions, but only grade(p) is used.
    Each coordinate omits one vertex per block; vertex 0 is always omitted.
    """
    bs = blocks(p)
    full = (1 << (len(p) - 1)) - 1
    row = 0
    for roots in product(*bs[1:]):
        omitted = 0
        for v in roots:
            omitted |= 1 << (v - 1)
        row |= 1 << (full ^ omitted)
    return row


def cut_feature(p: tuple[int, ...]) -> int:
    """Classical anchored cut row, used only as a comparison baseline."""
    bs = blocks(p)
    row = 0
    for selection in range(1 << (len(bs) - 1)):
        cut = 0
        for j, b in enumerate(bs[1:]):
            if selection & (1 << j):
                for v in b:
                    cut |= 1 << (v - 1)
        row |= 1 << cut
    return row


def source_digest(r: int, candidates: Iterable[Candidate]) -> str:
    obj = {"r": r, "candidates": sorted((c.record() for c in candidates), key=lambda c: c["id"])}
    return sha256(json.dumps(obj, sort_keys=True, separators=(",", ":"),
                             ensure_ascii=True).encode()).hexdigest()


def reduce_family(candidates: Iterable[Candidate], r: int, *,
                  method: str = "exterior", certificate: bool = True,
                  max_ports: int = 18, max_rows: int = 100000) -> tuple[list[Candidate], dict]:
    """Retain actual candidate IDs, choosing a cost-ordered basis per control/grade.

    The certificate consists of XOR dependence witnesses in terms of retained
    ORIGINAL rows. The function does not modify caller objects. Resource limits
    are checked before constructing any exponentially wide row.
    """
    if type(r) is not int or r < 1:
        raise ValueError("r must be a positive integer; closed roots are a separate case")
    if type(max_ports) is not int or max_ports < 1 or type(max_rows) is not int or max_rows < 0:
        raise ValueError("invalid resource caps")
    if r > max_ports:
        raise ResourceLimit("labelled interval limit exceeded")
    if method not in ("exterior", "cut"):
        raise ValueError("unknown basis method")
    if method == "cut" and certificate:
        raise ValueError("the independent certificate format is for exterior rows only")
    cs: list[Candidate] = []
    seen: set[str] = set()
    for c in candidates:
        if len(cs) >= max_rows:
            raise ResourceLimit("candidate limit exceeded")
        if not isinstance(c, Candidate):
            raise ValueError("expected Candidate")
        if not isinstance(c.id, str) or not c.id or c.id in seen:
            raise ValueError("IDs must be nonempty and unique")
        if not isinstance(c.control, str) or type(c.cost) is not int:
            raise ValueError("invalid control or cost")
        validate_partition(c.partition, r)
        seen.add(c.id)
        cs.append(c)
    cs.sort(key=lambda c: (c.cost, c.id))
    basis: dict[tuple[str, int], dict[int, tuple[int, int]]] = {}
    kept: list[Candidate] = []
    dropped: list[dict] = []
    xor_count = 0
    feature = exterior_feature if method == "exterior" else cut_feature
    for c in cs:
        key = (c.control, grade(c.partition))
        pivots = basis.setdefault(key, {})
        x = feature(c.partition)
        expression = 0
        while x:
            pivot = x.bit_length() - 1
            existing = pivots.get(pivot)
            if existing is None:
                j = len(kept)
                pivots[pivot] = (x, expression ^ (1 << j) if certificate else 0)
                kept.append(c)
                break
            x ^= existing[0]
            if certificate:
                expression ^= existing[1]
            xor_count += 1
        if not x and certificate:
            dropped.append({"id": c.id, "xor_hex": hex(expression)})
    stats = {"method": method, "input_rows": len(cs), "kept_rows": len(kept),
             "xor_count": xor_count,
             "per_grade": {str(d): sum(grade(c.partition) == d for c in kept) for d in range(r)}}
    if certificate:
        cert = {"version": 1, "r": r, "source_sha256": source_digest(r, cs),
                "kept": [c.id for c in kept], "dropped": dropped}
        return kept, {"certificate": cert, "stats": stats}
    return kept, {"stats": stats}


def top_pairing(p: tuple[int, ...], q: tuple[int, ...]) -> int:
    if len(p) != len(q) or grade(p) + grade(q) != len(p) - 1:
        return 0
    x, y = exterior_feature(p), exterior_feature(q)
    full = (1 << (len(p) - 1)) - 1
    ans = 0
    while x:
        bit = x & -x
        i = bit.bit_length() - 1
        ans ^= (y >> (full ^ i)) & 1
        x ^= bit
    return ans


def star_partition(r: int, subset: int) -> tuple[int, ...]:
    if type(r) is not int or r < 1 or type(subset) is not int or not 0 <= subset < (1 << (r-1)):
        raise ValueError("bad rooted subset")
    labels = [0]
    next_label = 1
    for v in range(1, r):
        if subset & (1 << (v-1)):
            labels.append(0)
        else:
            labels.append(next_label)
            next_label += 1
    return tuple(labels)
