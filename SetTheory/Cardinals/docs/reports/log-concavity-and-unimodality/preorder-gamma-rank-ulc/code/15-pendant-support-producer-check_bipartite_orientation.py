#!/usr/bin/env python3
"""Exact support-versus-transversal-merge check; Python standard library only."""
from collections import defaultdict
from itertools import combinations
import hashlib
import json
from pathlib import Path
import random
import time


def prod(values):
    r = 1
    for x in values:
        r *= x
    return r


def direct_supports(n, arcs):
    # Independent enumeration of physical directed matchings, followed by
    # deduplication of their ordered endpoint supports.
    out = {(0, 0)}
    for i, j in arcs:
        for s, t in list(out):
            if not ((s | t) & ((1 << i) | (1 << j))):
                out.add((s | (1 << i), t | (1 << j)))
    return out


def matchable(selected, positions, neighbors):
    if not selected:
        return True
    x, *rest = selected
    return any(matchable(rest, positions ^ (1 << c), neighbors)
               for c in range(positions.bit_length())
               if (positions & (1 << c)) and (neighbors[x] & (1 << c)))


def basis_terms(c, m, arcs, u, v, outgoing):
    # Enumerate ground subsets of a transversal matroid, not matchings.
    # Exterior element indices 0..m-1; private dummies m..m+c-1.
    neighbors = [0] * (m + c)
    for j in range(m):
        for a in range(c):
            arc = (a, c + j) if outgoing else (c + j, a)
            if arc in arcs:
                neighbors[j] |= 1 << a
    for a in range(c):
        neighbors[m + a] = 1 << a
    result = []
    for chosen in combinations(range(m + c), c):
        if not matchable(list(chosen), (1 << c) - 1, neighbors):
            continue
        exterior = sum(1 << i for i in chosen if i < m)
        unused = sum(1 << (i - m) for i in chosen if i >= m)
        used_core = ((1 << c) - 1) ^ unused
        core_activity = u if outgoing else v
        ext_activity = v if outgoing else u
        weight = prod(core_activity[a] for a in range(c)
                      if used_core & (1 << a))
        weight *= prod(ext_activity[c + j] for j in range(m)
                       if exterior & (1 << j))
        result.append((exterior, unused, weight))
    return result


def verify(c, m, arcs, u, v):
    n = c + m
    arcs = set(arcs)
    expected = defaultdict(int)
    gamma = [0] * (min(c, m) + 1)
    supports = direct_supports(n, arcs)
    for s, t in supports:
        used = s | t
        unused_core = ((1 << c) - 1) & ~used
        exterior = used >> c
        weight = prod(u[i] for i in range(n) if s & (1 << i))
        weight *= prod(v[i] for i in range(n) if t & (1 << i))
        if weight:
            expected[(unused_core, exterior)] += weight
        gamma[s.bit_count()] += weight
    actual = defaultdict(int)
    left = basis_terms(c, m, arcs, u, v, True)
    right = basis_terms(c, m, arcs, u, v, False)
    full = (1 << c) - 1
    for ext1, unused1, weight1 in left:
        for ext2, unused2, weight2 in right:
            if ext1 & ext2:
                continue
            # Merging core dummies kills a term iff neither dummy is present.
            if (unused1 | unused2) != full:
                continue
            key = (unused1 & unused2, ext1 | ext2)
            assert key[0].bit_count() + key[1].bit_count() == c
            if weight1 * weight2:
                actual[key] += weight1 * weight2
    assert dict(expected) == dict(actual), (c, m, sorted(arcs), expected, actual)
    assert expected[(full, 0)] == 1
    d = len(gamma) - 1
    while d and not gamma[d]:
        d -= 1
    for k in range(1, c):
        g = gamma + [0] * (c + 1 - len(gamma))
        assert k * (c - k) * g[k] ** 2 >= (k + 1) * (c - k + 1) * g[k-1] * g[k+1]
    return d == c


def main():
    start = time.monotonic()
    rng = random.Random(23503102026)
    tested = 0
    saturated = 0
    zero_faces = 0
    # Each of six physical edges can be absent, forward, reverse, or bidirected.
    for encoding in range(4 ** 6):
        arcs = []
        z = encoding
        for a in range(2):
            for j in range(3):
                value = z & 3
                z >>= 2
                if value & 1:
                    arcs.append((a, 2 + j))
                if value & 2:
                    arcs.append((2 + j, a))
        weights = [([1]*5, [1]*5),
                   ([rng.randrange(4) for _ in range(5)],
                    [rng.randrange(4) for _ in range(5)])]
        for u, v in weights:
            saturated += verify(2, 3, arcs, u, v)
            tested += 1
            zero_faces += int(0 in u + v)
        # Reverse the physical bipartition without changing physical arcs.
        rename = {0:3, 1:4, 2:0, 3:1, 4:2}
        reversed_arcs = [(rename[a], rename[b]) for a, b in arcs]
        saturated += verify(3, 2, reversed_arcs, [1]*5, [1]*5)
        tested += 1
    for trial in range(512):
        c, m = 3 + (trial % 2), 3 + ((trial // 2) % 3)
        n = c + m
        arcs = []
        for a in range(c):
            for j in range(m):
                value = rng.randrange(4)
                if value & 1:
                    arcs.append((a, c+j))
                if value & 2:
                    arcs.append((c+j, a))
        u = [rng.randrange(5) for _ in range(n)]
        v = [rng.randrange(5) for _ in range(n)]
        saturated += verify(c, m, arcs, u, v)
        tested += 1
        zero_faces += int(0 in u + v)
    result = {
        "result": "all exact support identities and cover-order inequalities passed",
        "exhaustive_directed_K2_3_relations": 4**6,
        "total_graph_weight_partition_tests": tested,
        "zero_activity_tests": zero_faces,
        "tests_saturating_chosen_part": saturated,
        "random_larger_cases": 512,
        "seed": 23503102026,
        "seconds": time.monotonic() - start,
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Exact computational checks corroborate the all-size Lorentzian proof; no deficient-rank normalization is inferred."
    }
    Path(__file__).with_name("verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
