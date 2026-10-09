"""Complete finite layered patch search under a common abstract arc-gluing contract.

Label 0 is a permanent, unglued marker. Non-root components may be forgotten.
No success returned here is a knot-recognition certificate.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from itertools import product
from typing import Iterable
import hashlib
import json
from .kernel import State, Candidate, ResourceLimit, reduce_candidates


@dataclass(frozen=True)
class Patch:
    incoming: int
    outgoing: int
    partition: tuple[int, ...]
    good: tuple[bool, ...]
    charges: tuple[int, ...]
    cost: int = 0
    q: int = 1

    def __post_init__(self) -> None:
        if any(type(x) is not int or x < 0 for x in (self.incoming, self.outgoing)):
            raise ValueError("port counts must be nonnegative integers")
        if type(self.cost) is not int or len(self.partition) != self.incoming + self.outgoing:
            raise ValueError("invalid patch cost or arity")
        if self.partition:
            State(self.partition, self.good, self.charges, self.q)  # same canonical syntax, without root semantics
        elif self.good or self.charges or type(self.q) is not int or self.q < 1 or self.q & (self.q - 1):
            raise ValueError("invalid empty patch")

    def as_dict(self) -> dict:
        return {"incoming": self.incoming, "outgoing": self.outgoing,
                "partition": list(self.partition), "good": list(self.good),
                "charges": list(self.charges), "cost": hex(self.cost), "q": self.q}

    @classmethod
    def from_dict(cls, d: dict) -> Patch:
        return cls(d["incoming"], d["outgoing"], tuple(d["partition"]),
                   tuple(d["good"]), tuple(d["charges"]), int(d["cost"], 16), d["q"])


@dataclass(frozen=True)
class Grammar:
    initial: tuple[Candidate, ...]
    layers: tuple[tuple[Patch, ...], ...]
    target: int | None = None
    geometry_key: str = "abstract-separated-arcs"

    def __post_init__(self) -> None:
        if not self.initial:
            raise ValueError("a grammar needs an initial family")
        r, q = self.initial[0].state.r, self.initial[0].state.q
        if any((c.state.r, c.state.q) != (r, q) for c in self.initial):
            raise ValueError("mixed initial interfaces")
        width = r - 1
        for layer in self.layers:
            if not layer:
                raise ValueError("each layer must list at least one option")
            next_width = layer[0].outgoing
            if any(p.incoming != width or p.outgoing != next_width or p.q != q for p in layer):
                raise ValueError("layer options must share their incoming/outgoing type")
            width = next_width
        if width:
            raise ValueError("last layer must consume all actual ports")
        if self.target is not None and (type(self.target) is not int or not 0 <= self.target < q):
            raise ValueError("invalid terminal charge target")
        if not isinstance(self.geometry_key, str):
            raise ValueError("geometry key must be a string")

    def as_dict(self) -> dict:
        return {"format": "rooted-patch-language-v1", "geometry_key": self.geometry_key,
                "target": self.target, "initial": [c.as_dict() for c in self.initial],
                "layers": [[p.as_dict() for p in layer] for layer in self.layers]}

    @classmethod
    def from_dict(cls, d: dict) -> Grammar:
        if d["format"] != "rooted-patch-language-v1":
            raise ValueError("unknown grammar format")
        initial = tuple(Candidate(State.from_dict(x["state"]), int(x["cost"], 16), tuple(x["witness"])) for x in d["initial"])
        return cls(initial, tuple(tuple(Patch.from_dict(p) for p in layer) for layer in d["layers"]),
                   d["target"], d["geometry_key"])

    def digest(self) -> str:
        return hashlib.sha256(json.dumps(self.as_dict(), sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def transition(state: State, patch: Patch) -> State:
    if patch.incoming != state.r - 1 or patch.q != state.q:
        raise ValueError("transition arity or charge group mismatch")
    offset = len(state.good)
    parent = list(range(offset + len(patch.good)))
    good = list(state.good + patch.good)
    charges = list(state.charges + patch.charges)
    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in range(patch.incoming):
        a, b = find(state.partition[i + 1]), find(offset + patch.partition[i])
        if a == b:
            good[a] = False
            charges[a] = 0
        else:
            parent[b] = a
            good[a] = good[a] and good[b]
            charges[a] = (charges[a] ^ charges[b]) if good[a] else 0
    # Quotient components without a surviving marker/port are deliberately absent.
    kept_vertices = [state.partition[0]] + [offset + patch.partition[patch.incoming + i]
                                          for i in range(patch.outgoing)]
    labels, flags, values, mapping = [], [], [], {}
    for vertex in kept_vertices:
        root = find(vertex)
        if root not in mapping:
            mapping[root] = len(mapping)
            flags.append(good[root]); values.append(charges[root] if good[root] else 0)
        labels.append(mapping[root])
    return State(tuple(labels), tuple(flags), tuple(values), state.q)


@dataclass
class SearchResult:
    status: str
    cost: int | None
    witness: tuple[int, ...] | None
    source_sha256: str
    transitions: int
    peak_exact_table: int
    peak_retained: int
    reductions: list[dict] = field(default_factory=list)

    def as_dict(self) -> dict:
        return {"status": self.status, "cost": None if self.cost is None else hex(self.cost),
                "witness": self.witness, "source_sha256": self.source_sha256,
                "transitions": self.transitions, "peak_exact_table": self.peak_exact_table,
                "peak_retained": self.peak_retained, "reductions": self.reductions}


def solve(grammar: Grammar, *, reduced: bool = True, certificates: bool = False,
          max_transitions: int | None = None, max_dimension: int = 2_000_000) -> SearchResult:
    if max_transitions is not None and (type(max_transitions) is not int or max_transitions < 0):
        raise ValueError("invalid transition limit")
    work, peak_before, peak_after, records = 0, 0, 0, []

    def compact(candidates: Iterable[Candidate], stage: int) -> list[Candidate]:
        nonlocal peak_before, peak_after
        table: dict[State, Candidate] = {}
        for c in candidates:
            if not c.state.good[0]:
                continue
            previous = table.get(c.state)
            if previous is None or c.cost < previous.cost or (c.cost == previous.cost and c.witness < previous.witness):
                table[c.state] = c
        family = list(table.values())
        peak_before = max(peak_before, len(family))
        if reduced:
            key = f"{grammar.digest()}:{grammar.geometry_key}:stage={stage}"
            original = family
            family, cert = reduce_candidates(family, geometry_key=key, certificate=certificates,
                                              max_dimension=max_dimension)
            if certificates:
                records.append({"candidates": [c.as_dict() for c in original], "certificate": cert})
        peak_after = max(peak_after, len(family))
        return family

    family = compact((Candidate(c.state, c.cost, (i,)) for i, c in enumerate(grammar.initial)), 0)
    for stage, layer in enumerate(grammar.layers, 1):
        generated = []
        for c in family:
            for i, patch in enumerate(layer):
                if max_transitions is not None and work >= max_transitions:
                    raise ResourceLimit("transition limit exhausted: no negative conclusion")
                work += 1
                state = transition(c.state, patch)
                if state.good[0]:
                    generated.append(Candidate(state, c.cost + patch.cost, c.witness + (i,)))
        family = compact(generated, stage)
    good = [c for c in family if c.state.good[0] and
            ((c.state.charges[0] != 0) if grammar.target is None else c.state.charges[0] == grammar.target)]
    best = min(good, key=lambda c: (c.cost, c.witness)) if good else None
    return SearchResult("FOUND_ABSTRACT_ROOTED_DISC" if best else "NO_ROOTED_DISC_IN_LANGUAGE",
                        None if best is None else best.cost, None if best is None else best.witness,
                        grammar.digest(), work, peak_before, peak_after, records)


def enumerate_assignments(grammar: Grammar):
    """Literal enumeration for bounded audits, not the optimized algorithm."""
    return product(range(len(grammar.initial)), *(range(len(layer)) for layer in grammar.layers))
