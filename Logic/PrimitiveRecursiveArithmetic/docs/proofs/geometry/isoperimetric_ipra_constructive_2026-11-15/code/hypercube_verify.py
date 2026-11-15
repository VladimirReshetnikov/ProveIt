#!/usr/bin/env python3
"""Exact finite checks for the hypercube manuscript. Tests are not a proof.

Vertex sets are masks over the vertices 0,...,2**d-1. Coordinate i is bit i.
All calculations are integer calculations; no floating point or logarithms.
"""
from __future__ import annotations
import argparse
import json
from math import comb
from pathlib import Path


def vertices(mask: int):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def simplicial_order(d: int) -> list[int]:
    return sorted(range(1 << d), key=lambda v: (v.bit_count(), tuple(-((v >> i) & 1) for i in range(d))))


def initial(d: int, k: int) -> int:
    return sum(1 << v for v in simplicial_order(d)[:k])


def neighborhood(d: int, mask: int) -> int:
    ans = mask
    for v in vertices(mask):
        for i in range(d):
            ans |= 1 << (v ^ (1 << i))
    return ans


def internal_edges(d: int, mask: int) -> int:
    return sum(bool(mask & (1 << (v ^ (1 << i)))) for v in vertices(mask) for i in range(d) if not (v >> i) & 1)


def edge_boundary(d: int, mask: int) -> int:
    return d * mask.bit_count() - 2 * internal_edges(d, mask)


def compress(d: int, mask: int, coordinate: int) -> int:
    counts = [0, 0]
    for v in vertices(mask):
        counts[(v >> coordinate) & 1] += 1
    result = 0
    lowmask = (1 << coordinate) - 1
    order = simplicial_order(d - 1)
    for bit in (0, 1):
        for w in order[:counts[bit]]:
            v = (w & lowmask) | ((w >> coordinate) << (coordinate + 1)) | (bit << coordinate)
            result |= 1 << v
    return result


def potential(d: int, mask: int) -> int:
    ranks = {v: r for r, v in enumerate(simplicial_order(d))}
    return sum(ranks[v] for v in vertices(mask))


def compression_certificate(d: int, mask: int) -> dict:
    trace = [mask]
    for _ in range(1 << (2 * d)):
        next_mask = mask
        for i in range(d):
            candidate = compress(d, mask, i)
            if candidate != mask:
                next_mask = candidate
                break
        if next_mask == mask:
            break
        assert next_mask.bit_count() == mask.bit_count()
        assert potential(d, next_mask) < potential(d, mask)
        assert neighborhood(d, next_mask).bit_count() <= neighborhood(d, mask).bit_count()
        trace.append(next_mask)
        mask = next_mask
    assert all(compress(d, mask, i) == mask for i in range(d))
    canonical = initial(d, mask.bit_count())
    assert neighborhood(d, canonical).bit_count() <= neighborhood(d, mask).bit_count()
    if d >= 3:
        assert neighborhood(d, canonical) & ~neighborhood(d, mask) == 0
    return {"dimension": d, "trace": trace, "final": mask, "canonical": canonical,
            "steps": len(trace) - 1, "step_bound": 1 << (2 * d)}


def is_subcube(d: int, mask: int) -> bool:
    if mask == 0:
        return False
    vs = list(vertices(mask))
    varying = 0
    for v in vs:
        varying |= v ^ vs[0]
    if len(vs) != 1 << varying.bit_count():
        return False
    return all((v ^ vs[0]) & ~varying == 0 for v in vs)


def exhaustive(d: int) -> dict:
    n = 1 << d
    total = 1 << n
    closed = [sum(1 << (v ^ (1 << i)) for i in range(d)) | (1 << v) for v in range(n)]
    open_nb = [closed[v] ^ (1 << v) for v in range(n)]
    neighborhoods = [0] * total
    edges = [0] * total
    g = [neighborhood(d, initial(d, k)).bit_count() for k in range(n + 1)]
    equality_count = 0
    for mask in range(total):
        if mask:
            low = mask & -mask
            v = low.bit_length() - 1
            prev = mask ^ low
            neighborhoods[mask] = neighborhoods[prev] | closed[v]
            edges[mask] = edges[prev] + (prev & open_nb[v]).bit_count()
        k = mask.bit_count()
        e = edges[mask]
        b = d * k - 2 * e
        assert (1 << (2 * e)) <= k ** k
        assert (1 << (d * k)) <= (1 << b) * k ** k
        assert neighborhoods[mask].bit_count() >= g[k]
        if k:
            equality = (1 << (2 * e)) == k ** k
            assert equality == is_subcube(d, mask)
            equality_count += equality
    assert equality_count == 3 ** d
    for r in range(d + 1):
        k = sum(comb(d, i) for i in range(r + 1))
        target = comb(d, r + 1) if r < d else 0
        assert g[k] - k == target
    # Exercise the constructive compression proof on a reproducible sample.
    samples = sorted({0, total - 1, *(s % total for s in (3, 19, 73, 1337, 49151, 52428, 43981))})
    certificates = [compression_certificate(d, s) for s in samples]
    return {"dimension": d, "sets_checked": total, "nonempty_edge_equalities": equality_count,
            "edge_and_vertex_inequalities": "passed", "binomial_thresholds": "passed",
            "sample_compression_certificates": certificates}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-dimension", type=int, default=4)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 0 <= args.max_dimension <= 4:
        parser.error("exhaustive mode is restricted to dimensions 0 through 4")
    result = {"purpose": "finite exact regression checks, not a substitute for the uniform proof",
              "results": [exhaustive(d) for d in range(args.max_dimension + 1)]}
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
