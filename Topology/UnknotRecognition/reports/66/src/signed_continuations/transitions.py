"""Small exact transition helpers. Geometry legality remains a separate input."""
from __future__ import annotations
from typing import Sequence
from .core import Candidate, SignedPartition, Reduction, reduce_family


def reduce_buckets(family: Sequence[Candidate], **limits) -> dict[tuple[int, str], Reduction]:
    buckets: dict[tuple[int, str], list[Candidate]] = {}
    for c in family:
        buckets.setdefault((c.partition.r, c.geometry_key), []).append(c)
    return {k: reduce_family(v, **limits) for k, v in buckets.items()}


def join_families(left: Sequence[Candidate], right: Sequence[Candidate], *,
                  key: str, charge: int = 0) -> list[Candidate]:
    """Compatible union of constraints; output key must be geometry-certified.

    This is not by itself topological gluing, which also owns cell charges.
    Tokens are local provenance references, not an expanded proof tree.
    """
    if type(charge) is not int:
        raise TypeError("charge must be an integer")
    out = []
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            p = a.partition.join(b.partition)
            if p is not None:
                out.append(Candidate(p, a.cost + b.cost + charge, f"join:{i}:{j}", key))
    return out


def optional_signed_edges(r: int, edges: Sequence[tuple[int,int,int,int]], *,
                           reduced: bool = True) -> tuple[list[Candidate], dict]:
    """Finite gain-constraint test workload, not a knot-recognition algorithm.

    Each edge tuple (u,v,c0,c1) permits skipping, equality for cost c0, or
    inequality for cost c1. Duplicate exact states keep only their cheapest
    witness. Every transition is generated from the current reduced family.
    """
    family = [Candidate(SignedPartition.discrete(r), 0, "root")]
    history = []; generated = 0; xors = 0
    for stage, (u,v,c0,c1) in enumerate(edges):
        candidates = list(family)
        for i, a in enumerate(family):
            for sign, cost in ((0,c0),(1,c1)):
                p = a.partition.add_edge(u,v,sign)
                if p is not None:
                    candidates.append(Candidate(p,a.cost+cost,f"{stage}:{i}:{sign}"))
        generated += len(candidates)
        best = {}
        for a in candidates:
            if a.partition not in best or a.cost < best[a.partition].cost:
                best[a.partition] = a
        family = list(best.values())
        before = len(family)
        if reduced:
            red = reduce_family(family)
            family = list(red.candidates); xors += red.xors
        history.append({"stage":stage,"before":before,"after":len(family)})
    return family, {"generated":generated,"xor_count":xors,"history":history}
