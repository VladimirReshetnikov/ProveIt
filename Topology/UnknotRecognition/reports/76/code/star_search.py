"""Nonnegative free-repetition search. NOT a fixed-span source simplifier.

This implements the rank-pumping corollary for an unconstrained Kleene-star
library. It must not be substituted for an exact-exponent query in a knot
region whose physical length is fixed.
"""
from __future__ import annotations
import heapq
from compressed_search import Candidate, compile_grammar, ResourceLimit
from disk_algebra import Morphism, compose, identity, feature


def star_summary(source: dict, *, max_accepted: int | None = 100000):
    program = compile_grammar(source)
    if len(program.rules) != 1 or program.rules[0].kind != "atoms":
        raise ValueError("star_summary accepts exactly one atoms node")
    atoms = program.rules[0].args
    if any(cost < 0 for _, cost, _ in atoms):
        raise ValueError("free-repetition optimization requires nonnegative atom costs")
    b = program.width
    queue = [(0, 0, identity(b).partition, 0, ())]
    ticket = 1
    pivots = {}
    accepted = []
    while queue:
        cost, _, p, charge, word = heapq.heappop(queue)
        row = feature(p)
        while row:
            key = charge, row.bit_length() - 1
            if key in pivots:
                row ^= pivots[key]
            else:
                if max_accepted is not None and len(accepted) >= max_accepted:
                    raise ResourceLimit("star basis budget exhausted")
                pivots[key] = row
                accepted.append(Candidate(p, cost, charge, word))
                for i, (q, w, h) in enumerate(atoms):
                    joined = compose(Morphism(b, b, p), Morphism(b, b, q))
                    if joined is not None:
                        heapq.heappush(queue, (cost+w, ticket, joined.partition, charge ^ h, word+(i,)))
                        ticket += 1
                break
    return accepted, {"accepted": len(accepted), "generated": ticket,
                      "max_word_length": max((len(x.origin) for x in accepted), default=0)}
