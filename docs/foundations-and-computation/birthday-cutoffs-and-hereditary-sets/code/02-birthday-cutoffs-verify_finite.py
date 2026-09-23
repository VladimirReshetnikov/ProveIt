#!/usr/bin/env python3
"""Finite checks for the coding conventions in article.tex.

Python 3.9+; standard library only. These are regression tests, not a formal
verification of the transfinite interpretation or of any forcing theorem.
Run from any directory: python code/verify_finite.py
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
from typing import FrozenSet, Iterable, Tuple
import json

Sign = Tuple[int, ...]
HF = FrozenSet["HF"]
Poly = Tuple[int, ...]  # coefficients of 1, omega, omega^2, ...


def sign_compare(a: Sign, b: Sign) -> int:
    """Lexicographic surreal order, with an ended word between -1 and +1."""
    for j in range(max(len(a), len(b))):
        x = a[j] if j < len(a) else 0
        y = b[j] if j < len(b) else 0
        if x != y:
            return -1 if x < y else 1
    return 0


def check_signs(max_length: int = 7) -> dict:
    words = tuple(s for n in range(max_length + 1)
                  for s in product((-1, 1), repeat=n))
    index = {s: i for i, s in enumerate(words)}
    # A bit records the truth value z < x, for every z of birthday < k.
    profiles = {}
    for k in range(max_length + 1):
        shorter = tuple(z for z in words if len(z) < k)
        profiles[k] = tuple(sum(1 << j for j, z in enumerate(shorter)
                                if sign_compare(z, x) < 0) for x in words)

    def formula_prefix(x: Sign, y: Sign) -> bool:
        return (len(x) <= len(y) and
                profiles[len(x)][index[x]] == profiles[len(x)][index[y]])

    prefix_count = 0
    for x in words:
        for y in words:
            assert formula_prefix(x, y) == (y[:len(x)] == x)
            prefix_count += 1
    bit_count = 0
    by_length = {k: tuple(x for x in words if len(x) == k)
                 for k in range(max_length + 1)}
    for s in words:
        for j in range(len(s)):
            bit = any(formula_prefix(u, s) and sign_compare(u, s) < 0
                      for u in by_length[j])
            assert bit == (s[j] == 1)
            bit_count += 1
    return {"max_sign_length": max_length, "sign_words": len(words),
            "prefix_pairs": prefix_count, "bit_positions": bit_count}


def normalize(a: Iterable[int]) -> Poly:
    values = list(a)
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def natural_add(a: Poly, b: Poly) -> Poly:
    return normalize((a[i] if i < len(a) else 0) +
                     (b[i] if i < len(b) else 0)
                     for i in range(max(len(a), len(b))))


def natural_mul(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return ()
    values = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            values[i + j] += x * y
    return normalize(values)


def ordinal_lt(a: Poly, b: Poly) -> bool:
    for i in reversed(range(max(len(a), len(b)))):
        x, y = (a[i] if i < len(a) else 0), (b[i] if i < len(b) else 0)
        if x != y:
            return x < y
    return False


def check_ordinal_addresses() -> dict:
    samples = tuple(normalize(a) for a in product(range(3), repeat=4))
    assert len(set(samples)) == 81
    count = 0
    for theta in samples:
        if not theta:
            continue
        below = tuple(a for a in samples if ordinal_lt(a, theta))
        bound = natural_add(natural_mul(theta, theta), theta)
        addresses = set()
        for x in below:
            for y in below:
                p = natural_add(natural_mul(theta, x), y)
                assert ordinal_lt(p, bound)
                assert p not in addresses
                addresses.add(p)
                count += 1
    return {"ordinal_polynomial_samples": len(samples),
            "ordinal_address_checks": count}


@dataclass(frozen=True)
class GraphCode:
    theta: int
    domain_word: Sign
    edge_word: Sign
    root: int

    @property
    def nodes(self) -> Tuple[int, ...]:
        return tuple(i for i, bit in enumerate(self.domain_word) if bit == 1)

    def edge(self, u: int, v: int) -> bool:
        return (u in self.nodes and v in self.nodes and
                self.edge_word[self.theta * u + v] == 1)


def subsets(nodes: Tuple[int, ...]):
    for mask in range(1 << len(nodes)):
        yield frozenset(u for j, u in enumerate(nodes) if mask & (1 << j))


@lru_cache(maxsize=None)
def predecessors(c: GraphCode, u: int) -> FrozenSet[int]:
    return frozenset(v for v in c.nodes if c.edge(v, u))


def closed(c: GraphCode, s: FrozenSet[int]) -> bool:
    return all(predecessors(c, u).issubset(s) for u in s)


@lru_cache(maxsize=None)
def valid(c: GraphCode) -> bool:
    n = c.theta
    if n <= 0 or len(c.domain_word) != n or len(c.edge_word) != n*n+n:
        return False
    if any(x not in (-1, 1) for x in c.domain_word + c.edge_word):
        return False
    nodes = c.nodes
    if c.root not in nodes:
        return False
    permitted = {n*u+v for u in nodes for v in nodes}
    if any(bit == 1 and j not in permitted for j, bit in enumerate(c.edge_word)):
        return False
    if len({predecessors(c, u) for u in nodes}) != len(nodes):
        return False
    for s in subsets(nodes):
        if s and not any(not (predecessors(c, u) & s) for u in s):
            return False
        if c.root in s and closed(c, s) and s != frozenset(nodes):
            return False
    return True


@lru_cache(maxsize=None)
def cone(c: GraphCode, root: int) -> FrozenSet[int]:
    """Literal finite version of the universal closed-subset formula."""
    result = frozenset(c.nodes)
    for s in subsets(c.nodes):
        if root in s and closed(c, s):
            result &= s
    # Independent finite reachability check.
    actual = {root}
    while True:
        expanded = actual | {v for u in actual for v in predecessors(c, u)}
        if expanded == actual:
            break
        actual = expanded
    assert result == frozenset(actual)
    return result


@lru_cache(maxsize=None)
def collapse(c: GraphCode, root: int) -> HF:
    return frozenset(collapse(c, v) for v in predecessors(c, root))


@lru_cache(maxsize=None)
def iso(c: GraphCode, a: int, d: GraphCode, b: int) -> bool:
    """Brute-force pointed graph isomorphism; does not compare collapses."""
    left, right = tuple(sorted(cone(c, a))), tuple(sorted(cone(d, b)))
    if len(left) != len(right):
        return False
    for perm in permutations(right):
        f = dict(zip(left, perm))
        if f[a] != b:
            continue
        if all(c.edge(u, v) == d.edge(f[u], f[v]) for u in left for v in left):
            rho = c.theta + d.theta + 1
            h = [-1] * (rho*rho + rho)
            for u, v in f.items():
                h[rho*u+v] = 1
            # Verify the witness really has the stipulated address graph.
            recovered = {(u, v) for u in left for v in right if h[rho*u+v] == 1}
            assert recovered == set(f.items())
            return True
    return False


def equality(c: GraphCode, d: GraphCode) -> bool:
    return valid(c) and valid(d) and iso(c, c.root, d, d.root)


def membership(c: GraphCode, d: GraphCode) -> bool:
    return valid(c) and valid(d) and any(
        iso(c, c.root, d, u) for u in predecessors(d, d.root))


def hf_key(x: HF) -> str:
    return "{" + ",".join(sorted(hf_key(y) for y in x)) + "}"


def tc_root(x: HF) -> Tuple[HF, ...]:
    result = {x}
    while True:
        enlarged = result | {y for z in result for y in z}
        if enlarged == result:
            return tuple(sorted(result, key=hf_key))
        result = enlarged


def encode(x: HF, labels: Tuple[int, ...] | None = None,
           theta: int | None = None) -> GraphCode:
    nodes = tc_root(x)
    if labels is None:
        labels = tuple(range(len(nodes)))
    if len(labels) != len(nodes) or len(set(labels)) != len(labels):
        raise ValueError("The labels must be distinct, one for each node.")
    theta = max(labels) + 1 if theta is None else theta
    if theta <= max(labels) or min(labels) < 0:
        raise ValueError("Labels must lie below the positive domain bound.")
    f = dict(zip(nodes, labels))
    domain = tuple(1 if u in labels else -1 for u in range(theta))
    edge = [-1] * (theta*theta + theta)
    for v in nodes:
        for u in v:
            edge[theta*f[u]+f[v]] = 1
    return GraphCode(theta, domain, tuple(edge), f[x])


def check_graphs() -> dict:
    universe: FrozenSet[HF] = frozenset()
    for _ in range(4):
        values = tuple(universe)
        universe = frozenset(frozenset(values[j] for j in range(len(values))
                                       if mask & (1 << j))
                             for mask in range(1 << len(values)))
    roots = tuple(sorted(universe, key=hf_key))  # all 16 elements of V_4
    assert len(roots) == 16
    representatives = []
    relabelling_count = 0
    for x in roots:
        base = encode(x)
        assert valid(base) and collapse(base, base.root) == x
        n = len(base.nodes)
        for labels in permutations(range(n)):
            c = encode(x, labels)
            assert valid(c)
            assert collapse(c, c.root) == x
            assert iso(base, base.root, c, c.root)
            relabelling_count += 1
        # A non-full domain with spare labels checks the domain-mask convention.
        padded = encode(x, tuple(2*j+1 for j in reversed(range(n))), 2*n+1)
        assert valid(padded) and equality(base, padded)
        representatives.extend((base, padded))

    pair_count = 0
    for c in representatives:
        for d in representatives:
            x, y = collapse(c, c.root), collapse(d, d.root)
            assert equality(c, d) == (x == y)
            assert membership(c, d) == (x in y)
            pair_count += 1

    # Intentionally bad shapes/relations: self-loop, duplicate empty nodes,
    # unreachable node, and a positive unused address.
    loop = GraphCode(1, (1,), (1, -1), 0)
    duplicate = GraphCode(2, (1, 1), (-1,)*6, 0)
    edge = [-1]*6
    edge[1] = 1  # 0 E 1, but 0 is the root: 1 is unreachable.
    unreachable = GraphCode(2, (1, 1), tuple(edge), 0)
    unused = GraphCode(1, (1,), (-1, 1), 0)
    for bad in (loop, duplicate, unreachable, unused):
        assert not valid(bad)
    return {"hereditarily_finite_roots": len(roots),
            "relabellings_checked": relabelling_count,
            "equality_and_membership_pairs": pair_count,
            "invalid_codes_rejected": 4}


def main() -> None:
    results = {"status": "all checks passed", "proof_status": "finite regression tests only"}
    results.update(check_signs())
    results.update(check_ordinal_addresses())
    results.update(check_graphs())
    out = Path(__file__).resolve().parents[1] / "data"
    out.mkdir(exist_ok=True)
    (out / "verification.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    text = ("The executed finite regression suite passed all "
            f"{results['prefix_pairs']:,} sign-prefix comparisons and "
            f"{results['bit_positions']:,} bit-position checks through sign length 7. "
            f"It also checked {results['ordinal_address_checks']:,} natural-ordinal "
            "matrix addresses on finite Cantor-normal-form samples, "
            f"{results['relabellings_checked']:,} relabellings of all 16 sets in "
            "$V_4$, and "
            f"{results['equality_and_membership_pairs']:,} pairs of graph codes for "
            "both equality and membership. Four intentionally invalid codes were "
            "rejected. All calculations used the Python standard library.\n")
    (out / "verification_summary.tex").write_text(text, encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
