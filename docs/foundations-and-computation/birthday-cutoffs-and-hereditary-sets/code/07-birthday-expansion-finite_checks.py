#!/usr/bin/env python3
"""Finite checks for The Birthday Expansion of the Surreal Field.

No external packages are needed. Run with Python 3.10 or later:
    python finite_checks.py --output finite_checks_output.json

These exhaustive finite tests are NOT proofs of any transfinite, class-sized,
or model-theoretic assertion in the article.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
from typing import FrozenSet

Sign = tuple[int, ...]  # -1 is minus; +1 is plus; missing means 0.


def compare_signs(a: Sign, b: Sign) -> int:
    """Numerical order of finite signs: minus < missing < plus."""
    for i in range(max(len(a), len(b))):
        ai = a[i] if i < len(a) else 0
        bi = b[i] if i < len(b) else 0
        if ai != bi:
            return 1 if ai > bi else -1
    return 0


def check_signs(max_length: int = 6) -> dict[str, int]:
    signs = [s for n in range(max_length + 1) for s in product((-1, 1), repeat=n)]
    order = {(a, b): compare_signs(a, b) for a in signs for b in signs}
    pref: dict[tuple[Sign, Sign], bool] = {}
    pair_count = 0
    for u in signs:
        short = [z for z in signs if len(z) < len(u)]
        for x in signs:
            between = any(
                (order[u, z] < 0 and order[z, x] < 0)
                or (order[x, z] < 0 and order[z, u] < 0)
                for z in short
            )
            defined = len(u) <= len(x) and not between
            actual = len(u) <= len(x) and x[:len(u)] == u
            assert defined == actual, ("Prefix disagreement", u, x)
            pref[u, x] = defined
            pair_count += 1
    bit_count = 0
    for x in signs:
        for alpha in range(len(x)):
            defined = any(
                len(u) == alpha and pref[u, x] and order[u, x] < 0 for u in signs
            )
            assert defined == (x[alpha] == 1), ("Bit disagreement", x, alpha)
            bit_count += 1
    return {"sign_strings": len(signs), "prefix_pairs": pair_count,
            "individual_signs": bit_count}


def check_radices() -> dict[str, int]:
    """Check q = omega^r, 1 <= r <= 3, using finite ordinal polynomials.

    Coefficient tuples run from constant term upwards. For a,c < omega^r,
    natural multiplication by omega^r shifts a upwards by r exponents;
    natural addition is coefficientwise. Coefficients are drawn from {0,1,2}.
    """
    count = 0
    for r in range(1, 4):
        below_q = list(product(range(3), repeat=r))
        seen: set[tuple[int, ...]] = set()
        for a in below_q:
            for c in below_q:
                # Addition of disjoint coefficient blocks is literal concatenation.
                encoded = c + a
                assert encoded not in seen, ("Address collision", r, a, c)
                seen.add(encoded)
                assert encoded[:r] == c and encoded[r:] == a
                assert len(encoded) == 2 * r  # Exponents are strictly below 2r.
                count += 1
        assert len(seen) == len(below_q) ** 2
    return {"radices": 3, "addresses": count}


@dataclass(frozen=True)
class Graph:
    n: int
    edges: FrozenSet[tuple[int, int]]  # (u,v) means u is an element-predecessor of v.
    root: int

    def predecessors(self, v: int) -> FrozenSet[int]:
        return frozenset(u for u, w in self.edges if w == v)


def accessible(g: Graph) -> bool:
    reached = {g.root}
    while True:
        enlarged = reached | {u for u, v in g.edges if v in reached}
        if enlarged == reached:
            return len(reached) == g.n
        reached = enlarged


def collapse(g: Graph) -> frozenset:
    """Finite Mostowski-style collapse; reject cycles explicitly."""
    active: set[int] = set()
    cache: dict[int, frozenset] = {}

    def visit(v: int) -> frozenset:
        if v in active:
            raise ValueError("A cycle was encountered.")
        if v not in cache:
            active.add(v)
            cache[v] = frozenset(visit(u) for u in g.predecessors(v))
            active.remove(v)
        return cache[v]

    value = visit(g.root)
    assert len(cache) == g.n
    assert len(set(cache.values())) == g.n, "Non-extensional collapse"
    return value


def relabel(g: Graph, labels: tuple[int, ...]) -> Graph:
    return Graph(g.n, frozenset((labels[u], labels[v]) for u, v in g.edges),
                 labels[g.root])


def graph_family(max_nodes: int = 4) -> tuple[list[Graph], int]:
    """All retained upper-triangular graphs, then all permutations of labels."""
    all_graphs: set[Graph] = set()
    canonical_count = 0
    for n in range(1, max_nodes + 1):
        possible = [(u, v) for v in range(n) for u in range(v)]
        for bits in product((False, True), repeat=len(possible)):
            g = Graph(n, frozenset(e for e, present in zip(possible, bits) if present),
                      n - 1)
            # Triangular edge direction ensures well-foundedness.
            if len({g.predecessors(v) for v in range(n)}) != n or not accessible(g):
                continue
            canonical_count += 1
            expected = collapse(g)
            for labels in permutations(range(n)):
                renamed = relabel(g, labels)
                assert collapse(renamed) == expected
                all_graphs.add(renamed)
    return sorted(all_graphs, key=lambda g: (g.n, g.root, sorted(g.edges))), canonical_count


@lru_cache(maxsize=None)
def injections(m: int, n: int) -> tuple[tuple[int, ...], ...]:
    return tuple(permutations(range(n), m)) if m <= n else ()


def preserves_edges(g: Graph, h: Graph, f: tuple[int, ...]) -> bool:
    return all(((u, v) in g.edges) == ((f[u], f[v]) in h.edges)
               for u in range(g.n) for v in range(g.n))


def isomorphic(g: Graph, h: Graph) -> bool:
    if g.n != h.n:
        return False
    return any(f[g.root] == h.root and preserves_edges(g, h, f)
               for f in injections(g.n, h.n))


def membership_code(g: Graph, h: Graph, require_closed_range: bool = True) -> bool:
    for f in injections(g.n, h.n):
        if (f[g.root], h.root) not in h.edges or not preserves_edges(g, h, f):
            continue
        image = set(f)
        if require_closed_range and any(v in image and u not in image for u, v in h.edges):
            continue
        return True
    return False


def check_graphs() -> dict[str, int | bool]:
    graphs, canonical_count = graph_family()
    values = {g: collapse(g) for g in graphs}
    pair_count = 0
    for g in graphs:
        for h in graphs:
            assert isomorphic(g, h) == (values[g] == values[h]), ("Isomorphism", g, h)
            assert membership_code(g, h) == (values[g] in values[h]), ("Membership", g, h)
            pair_count += 1
    # Empty-set source and singleton-of-singleton target: a one-vertex map
    # onto the target's nonempty predecessor wrongly succeeds without closure.
    empty = Graph(1, frozenset(), 0)
    singleton_singleton = Graph(3, frozenset({(0, 1), (1, 2)}), 2)
    assert values[empty] not in values[singleton_singleton]
    assert membership_code(empty, singleton_singleton, require_closed_range=False)
    assert not membership_code(empty, singleton_singleton)
    return {"initial_triangular_graphs": canonical_count,
            "graphs_including_all_relabelings": len(graphs),
            "decoded_sets": len(set(values.values())),
            "isomorphism_pairs": pair_count, "membership_pairs": pair_count,
            "missing_range_condition_counterexample_confirmed": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON output file.")
    args = parser.parse_args()
    report = {"status": "all finite checks passed", "signs": check_signs(),
              "ordinal_polynomial_addresses": check_radices(), "graphs": check_graphs(),
              "scope": "Finite consistency checks only; not a proof of transfinite results."}
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
