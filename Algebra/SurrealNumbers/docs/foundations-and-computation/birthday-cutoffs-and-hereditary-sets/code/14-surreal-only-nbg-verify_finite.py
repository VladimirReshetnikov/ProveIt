#!/usr/bin/env python3
"""Finite sanity checks for article.tex; NOT a proof of its transfinite theorems.

No third-party dependencies. Run: python3 verify_finite.py
Output: verification.json next to this script.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import json

Sign = tuple[int, ...]  # -1 is minus; +1 is plus


def signs(max_length: int) -> list[Sign]:
    return [s for n in range(max_length + 1) for s in product((-1, 1), repeat=n)]


def lt(a: Sign, b: Sign) -> bool:
    """Surreal sign order, with end of sequence between minus and plus."""
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else 0
        y = b[i] if i < len(b) else 0
        if x != y:
            return x < y
    return False


def prefix_formula(p: Sign, x: Sign, universe: list[Sign]) -> bool:
    return len(p) <= len(x) and all(
        lt(z, p) == lt(z, x) for z in universe if len(z) < len(p)
    )


def sign_value(s: Sign) -> Fraction:
    if not s:
        return Fraction(0)
    r = 1
    while r < len(s) and s[r] == s[0]:
        r += 1
    value = Fraction(s[0] * r)
    for k, bit in enumerate(s[r:], start=1):
        value += Fraction(bit, 2**k)
    return value


def dyadic_birthday(x: Fraction) -> int:
    y = abs(x)
    d = y.denominator
    if d & (d - 1):
        raise ValueError("Expected a dyadic rational")
    if d == 1:
        return y.numerator
    return y.numerator // d + (d.bit_length() - 1) + 1


def pair(a: int, b: int) -> int:
    return (a + b) ** 2 + a


def bound(d: int) -> int:
    return (d + d) ** 2 + d + 1


# CNF polynomials in omega, low-degree-first coefficients.
def norm(p: tuple[int, ...]) -> tuple[int, ...]:
    q = list(p)
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return tuple(q)


def padd(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    n = max(len(p), len(q))
    return norm(tuple((p[i] if i < len(p) else 0) +
                      (q[i] if i < len(q) else 0) for i in range(n)))


def pmul(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return norm(tuple(result))


def pcmp(p: tuple[int, ...], q: tuple[int, ...]) -> int:
    n = max(len(p), len(q))
    p = p + (0,) * (n - len(p))
    q = q + (0,) * (n - len(q))
    return (p[::-1] > q[::-1]) - (p[::-1] < q[::-1])


def ppair(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    s = padd(a, b)
    return padd(pmul(s, s), a)


@dataclass(frozen=True)
class Graph:
    n: int
    root: int
    edges: frozenset[tuple[int, int]]  # (child, parent)

    def hull(self, root: int) -> frozenset[int]:
        result = {root}
        while True:
            new = result | {i for i, j in self.edges if j in result}
            if new == result:
                return frozenset(result)
            result = new

    def valid(self) -> bool:
        predecessors = [frozenset(i for i, j in self.edges if j == v)
                        for v in range(self.n)]
        if len(set(predecessors)) != self.n:
            return False
        if self.hull(self.root) != frozenset(range(self.n)):
            return False
        # Every nonempty subset must have an E-minimal member.
        for mask in range(1, 1 << self.n):
            members = [i for i in range(self.n) if mask >> i & 1]
            if not any(not any((j, i) in self.edges for j in members)
                       for i in members):
                return False
        return True

    def collapse(self) -> frozenset:
        @lru_cache(None)
        def visit(v: int) -> frozenset:
            return frozenset(visit(i) for i, j in self.edges if j == v)
        return visit(self.root)

    def permute(self, p: tuple[int, ...]) -> Graph:
        return Graph(self.n, p[self.root],
                     frozenset((p[i], p[j]) for i, j in self.edges))

    def encode(self) -> tuple[int, ...]:
        bits = [0] * bound(self.n)
        for i, j in self.edges:
            bits[pair(i, j)] = 1
        return tuple(bits)


def isomorphic(a: Graph, b: Graph, root: int | None = None) -> bool:
    root = b.root if root is None else root
    target = sorted(b.hull(root))
    if len(target) != a.n:
        return False
    for perm in permutations(target):
        if perm[a.root] != root:
            continue
        if all(((i, j) in a.edges) == ((perm[i], perm[j]) in b.edges)
               for i in range(a.n) for j in range(a.n)):
            return True
    return False


def member_code(a: Graph, b: Graph) -> bool:
    return any(isomorphic(a, b, j) for j, r in b.edges if r == b.root)


def pack(a: Sign, b: Sign) -> Sign:
    return tuple(v for bit in a for v in (1, bit)) + (-1, -1) + \
           tuple(v for bit in b for v in (1, bit))


def unpack(s: Sign) -> tuple[Sign, Sign]:
    if len(s) % 2:
        raise ValueError("Malformed packed code")
    blocks = [s[i:i + 2] for i in range(0, len(s), 2)]
    delimiters = [i for i, block in enumerate(blocks) if block == (-1, -1)]
    if len(delimiters) != 1:
        raise ValueError("Expected exactly one delimiter")
    d = delimiters[0]
    if any(x != d and block[0] != 1 for x, block in enumerate(blocks)):
        raise ValueError("Malformed data block")
    return tuple(t[1] for t in blocks[:d]), tuple(t[1] for t in blocks[d + 1:])


def main() -> None:
    result: dict[str, object] = {
        "status": "passed",
        "scope": "Finite sanity checks only, not formal or transfinite proofs.",
    }
    universe = signs(6)
    prefix_checks = 0
    bit_checks = 0
    for p in universe:
        for x in universe:
            expected = len(p) <= len(x) and x[:len(p)] == p
            assert prefix_formula(p, x, universe) == expected
            prefix_checks += 1
    for x in universe:
        for alpha in range(len(x)):
            prefixes = [p for p in universe if len(p) == alpha and
                        prefix_formula(p, x, universe)]
            assert len(prefixes) == 1
            assert lt(prefixes[0], x) == (x[alpha] == 1)
            bit_checks += 1
    result["sign_prefix_pairs"] = prefix_checks
    result["sign_bit_checks"] = bit_checks

    finite_codes = {pair(i, j) for i in range(80) for j in range(80)}
    assert len(finite_codes) == 80**2
    assert max(finite_codes) < bound(80)
    result["finite_ordinal_pairs"] = len(finite_codes)

    polys = [norm(p) for p in product(range(4), repeat=3)]
    poly_codes = {ppair(a, b) for a in polys for b in polys}
    assert len(poly_codes) == len(polys)**2
    delta = (4, 4, 4)
    twice = padd(delta, delta)
    limit = padd(padd(pmul(twice, twice), delta), (1,))
    assert all(pcmp(p, limit) < 0 for p in poly_codes)
    result["cantor_normal_form_pairs"] = len(poly_codes)

    graphs: set[Graph] = set()
    dag_candidates = 0
    for n in range(1, 5):
        options = [(i, j) for j in range(n) for i in range(j)]
        for mask in range(1 << len(options)):
            dag_candidates += 1
            g = Graph(n, n - 1, frozenset(edge for k, edge in enumerate(options)
                                          if mask >> k & 1))
            if g.valid():
                for perm in permutations(range(n)):
                    graphs.add(g.permute(perm))
    graphs_list = list(graphs)
    for g in graphs_list:
        assert g.valid()
        bits = g.encode()
        assert len(bits) == bound(g.n)
        recovered = frozenset((i, j) for i in range(g.n) for j in range(g.n)
                              if bits[pair(i, j)])
        assert recovered == g.edges
    for a in graphs_list:
        for b in graphs_list:
            assert isomorphic(a, b) == (a.collapse() == b.collapse())
            assert member_code(a, b) == (a.collapse() in b.collapse())
    result["increasing_DAG_candidates"] = dag_candidates
    result["valid_labelled_rooted_graphs"] = len(graphs)
    result["graph_equality_comparisons"] = len(graphs)**2
    result["graph_membership_comparisons"] = len(graphs)**2

    small_signs = signs(4)
    packed = {pack(a, b) for a in small_signs for b in small_signs}
    assert len(packed) == len(small_signs)**2
    for a in small_signs:
        for b in small_signs:
            assert unpack(pack(a, b)) == (a, b)
    result["finite_tuple_pack_roundtrips"] = len(packed)

    for s in signs(8):
        assert dyadic_birthday(sign_value(s)) == len(s)
    qchecks = 0
    for a in range(-24, 25):
        for b in (1, 2, 4, 8, 16):
            for k in (-5, -2, 1, 3, 6):
                assert Fraction(a, b) == Fraction(k*a, k*b)
                assert dyadic_birthday(Fraction(a, b)) == \
                       dyadic_birthday(Fraction(k*a, k*b))
                qchecks += 1
    assert dyadic_birthday(Fraction(1, 2)) == 2
    result["dyadic_sign_birthday_checks"] = len(signs(8))
    result["dyadic_fraction_invariance_checks"] = qchecks

    matrix_checks = 0
    for n in range(1, 5):
        for matrix in range(1 << (n*n)):
            rows = [(matrix >> (n*i)) & ((1 << n) - 1) for i in range(n)]
            diagonal = sum((1 - ((rows[i] >> i) & 1)) << i for i in range(n))
            assert all(row != diagonal for row in rows)
            matrix_checks += 1
    result["boolean_matrices_diagonal_checked"] = matrix_checks

    path = Path(__file__).with_name("verification.json")
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
