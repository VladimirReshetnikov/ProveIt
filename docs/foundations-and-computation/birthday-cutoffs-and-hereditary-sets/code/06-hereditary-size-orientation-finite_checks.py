#!/usr/bin/env python3
"""Finite regression checks for 'What Birthday-Enriched Surreal Fields Remember'.

Standard-library only; Python 3.10 or later. These tests are NOT proofs of the
transfinite, model-theoretic, Choice, or forcing theorems in the article.
No assertions depend on the optimization-sensitive Python `assert` statement.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product, permutations
from typing import TypeAlias

Word: TypeAlias = tuple[int, ...]
HF: TypeAlias = frozenset["HF"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def compare_words(x: Word, y: Word) -> int:
    """First-difference order: minus < termination < plus."""
    for k in range(max(len(x), len(y))):
        a = 2 * x[k] - 1 if k < len(x) else 0
        b = 2 * y[k] - 1 if k < len(y) else 0
        if a != b:
            return (a > b) - (a < b)
    return 0


def test_sign_formulas(max_length: int = 6) -> None:
    words = [tuple(w) for n in range(max_length + 1)
             for w in product((0, 1), repeat=n)]
    comparisons = {(x, y): compare_words(x, y) for x in words for y in words}
    prefixes: dict[tuple[Word, Word], bool] = {}
    prefix_checks = 0
    for x in words:
        shorter = [z for z in words if len(z) < len(x)]
        for y in words:
            formula = len(x) <= len(y) and all(
                (comparisons[z, x] < 0) == (comparisons[z, y] < 0)
                and (comparisons[x, z] < 0) == (comparisons[y, z] < 0)
                for z in shorter)
            actual = len(x) <= len(y) and x == y[:len(x)]
            require(formula == actual, f"Prefix disagreement: {x}, {y}")
            prefixes[x, y] = formula
            prefix_checks += 1
    bit_checks = 0
    for s in words:
        for alpha in range(len(s)):
            formula = any(len(t) == alpha and prefixes[t, s]
                          and comparisons[t, s] < 0 for t in words)
            require(formula == (s[alpha] == 1), f"Bit disagreement: {s}, {alpha}")
            bit_checks += 1
    print(f"PASS: {len(words)} words, length <= {max_length}; "
          f"{prefix_checks} prefix instances, {bit_checks} bit instances.")


def pairing(a: int, b: int) -> int:
    return (a + b) ** 2 + a


def test_finite_pairing(bound: int = 100) -> None:
    seen: dict[int, tuple[int, int]] = {}
    for a in range(bound):
        for b in range(bound):
            p = pairing(a, b)
            require(p not in seen, f"Pairing collision: {a}, {b}, {seen.get(p)}")
            seen[p] = a, b
            require(p < pairing(bound, bound) + 1, "Pairing bound failure")
            require(pairing(a + 1, b) > p, "First-coordinate monotonicity failure")
            require(pairing(a, b + 1) > p, "Second-coordinate monotonicity failure")
    print(f"PASS: pairing injectivity, bound and monotonicity on {bound ** 2} pairs.")


@dataclass(frozen=True)
class GraphCode:
    n: int
    predecessors: tuple[int, ...]
    root: int
    values: tuple[HF, ...]

    @property
    def value(self) -> HF:
        return self.values[self.root]

    def edge(self, u: int, v: int) -> bool:
        return bool(self.predecessors[v] & (1 << u))


def well_founded(pred: tuple[int, ...]) -> bool:
    n = len(pred)
    return all(any(a & (1 << v) and not (pred[v] & a) for v in range(n))
               for a in range(1, 1 << n))


def root_generated(pred: tuple[int, ...], root: int) -> bool:
    n = len(pred)
    full = (1 << n) - 1
    for a in range(1 << n):
        if not (a & (1 << root)):
            continue
        downward_closed = all(not (a & (1 << v)) or pred[v] & ~a == 0
                              for v in range(n))
        if downward_closed and a != full:
            return False
    return True


def collapse(pred: tuple[int, ...]) -> tuple[HF, ...]:
    n = len(pred)
    values: dict[int, HF] = {}
    while len(values) < n:
        progress = False
        for v in range(n):
            if v in values:
                continue
            predecessors = [u for u in range(n) if pred[v] & (1 << u)]
            if all(u in values for u in predecessors):
                values[v] = frozenset(values[u] for u in predecessors)
                progress = True
        if not progress:
            raise ValueError("Cyclic input supplied to collapse")
    return tuple(values[v] for v in range(n))


def transitive_closure_of_singleton(x: HF) -> frozenset[HF]:
    visited: set[HF] = set()
    pending = [x]
    while pending:
        y = pending.pop()
        if y not in visited:
            visited.add(y)
            pending.extend(y)
    return frozenset(visited)


def equivalent(c: GraphCode, d: GraphCode) -> bool:
    if c.n != d.n:
        return False
    return any(f[c.root] == d.root and all(
        c.edge(u, v) == d.edge(f[u], f[v])
        for u in range(c.n) for v in range(c.n))
        for f in permutations(range(d.n)))


def member(c: GraphCode, d: GraphCode) -> bool:
    if c.n > d.n:
        return False
    for f in permutations(range(d.n), c.n):
        if not d.edge(f[c.root], d.root):
            continue
        if not all(c.edge(u, v) == d.edge(f[u], f[v])
                   for u in range(c.n) for v in range(c.n)):
            continue
        image = set(f)
        if all(not d.edge(w, f[u]) or w in image
               for u in range(c.n) for w in range(d.n)):
            return True
    return False


def test_finite_codes(max_vertices: int = 3) -> None:
    codes: list[GraphCode] = []
    rooted_relations = 0
    wf_relations = 0
    for n in range(1, max_vertices + 1):
        for mask in range(1 << (n * n)):
            pred = tuple(sum((1 << u) for u in range(n)
                             if mask & (1 << (u * n + v))) for v in range(n))
            wf = well_founded(pred)
            ext = len(set(pred)) == n
            vals = collapse(pred) if wf else None
            wf_relations += int(wf)
            for root in range(n):
                rooted_relations += 1
                generated = root_generated(pred, root)
                if wf:
                    require(vals is not None, "Missing collapse")
                    require(ext == (len(set(vals)) == n),
                            f"Extensionality-collapse mismatch: {pred}")
                    tc = transitive_closure_of_singleton(vals[root])
                    # Equality of collapsed range alone cannot test root generation
                    # unless collapse is injective. Restrict this check to Ext.
                    if ext:
                        require(generated == (set(vals) == set(tc)),
                                "Root-generation/collapse mismatch")
                    if ext and generated:
                        require(len(tc) == n, "Hereditary-size equality failure")
                        codes.append(GraphCode(n, pred, root, vals))
    equality_checks = membership_checks = 0
    for c in codes:
        for d in codes:
            require(equivalent(c, d) == (c.value == d.value),
                    "Code-equivalence correctness failure")
            require(member(c, d) == (c.value in d.value),
                    "Code-membership correctness failure")
            equality_checks += 1
            membership_checks += 1
    print(f"PASS: all {rooted_relations} rooted relations on 1..{max_vertices} vertices;")
    print(f"      {wf_relations} well-founded unrooted relations, {len(codes)} valid codes,")
    print(f"      {equality_checks} equivalence and {membership_checks} membership comparisons.")


def main() -> None:
    print("Finite formula regression checks")
    print("These are finite tests, NOT proofs of the article's infinite theorems.\n")
    test_sign_formulas()
    test_finite_pairing()
    test_finite_codes()
    print("\nAll stated finite tests passed.")


if __name__ == "__main__":
    main()
