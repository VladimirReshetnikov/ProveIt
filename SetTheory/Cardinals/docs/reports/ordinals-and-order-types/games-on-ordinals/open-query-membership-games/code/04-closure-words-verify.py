#!/usr/bin/env python3
"""Exact finite checks for Closure-Word Duality (Python standard library).

Finite topology checks do not verify the infinite-space proofs.  Run without
-O: assertions are verification conditions.  No network or third-party modules.
"""
from __future__ import annotations
import argparse
from collections import deque
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import platform
import time

Word = tuple[int, ...]
INF = 10**9


def reduce_word(w: Word) -> Word:
    return tuple(a for i, a in enumerate(w) if i == 0 or a != w[i - 1])


def is_subsequence(v: Word, w: Word) -> bool:
    j = 0
    for a in w:
        if j < len(v) and v[j] == a:
            j += 1
    return j == len(v)


def reduced_words(q: int, length: int):
    if length == 0:
        yield ()
    else:
        for w in reduced_words(q, length - 1):
            for a in range(q):
                if not w or w[-1] != a:
                    yield w + (a,)


def maximal_basis(words: tuple[Word, ...]) -> tuple[Word, ...]:
    out: list[Word] = []
    for w in sorted(set(words), key=lambda z: (-len(z), z)):
        if not any(is_subsequence(w, v) for v in out):
            out.append(w)
    return tuple(sorted(out))


@lru_cache(maxsize=None)
def shortest_supersequence(basis: tuple[Word, ...], q: int) -> Word:
    """Breadth-first search of greedy progress states; returns a certificate."""
    start = (0,) * len(basis)
    goal = tuple(map(len, basis))
    queue = deque([start])
    pred: dict[tuple[int, ...], tuple[tuple[int, ...], int] | None] = {start: None}
    while queue:
        state = queue.popleft()
        if state == goal:
            letters: list[int] = []
            while pred[state] is not None:
                previous, a = pred[state]  # type: ignore[misc]
                letters.append(a)
                state = previous
            return tuple(reversed(letters))
        for a in range(q):
            nxt = tuple(j + int(j < len(w) and w[j] == a)
                        for w, j in zip(basis, state))
            if nxt not in pred:
                pred[nxt] = (state, a)
                queue.append(nxt)
    raise AssertionError("Every finite family has a common supersequence")


def separating_word(basis: tuple[Word, ...], avoided: Word) -> Word:
    """A common supersequence avoiding avoided, when every input avoids it."""
    if not avoided:
        raise ValueError("The avoided word must be nonempty")
    blocks: list[list[int]] = [[] for _ in avoided]
    for w in basis:
        stage = 0
        for a in w:
            if a == avoided[stage]:
                stage += 1
                if stage == len(avoided):
                    raise ValueError("An input contains the avoided word")
            else:
                blocks[stage].append(a)
    out: list[int] = []
    for i, block in enumerate(blocks):
        out.extend(block)
        if i + 1 < len(blocks):
            out.append(avoided[i])
    result = reduce_word(tuple(out))
    assert all(is_subsequence(w, result) for w in basis)
    assert not is_subsequence(avoided, result)
    assert len(result) <= sum(map(len, basis)) + len(avoided) - 1
    return result


def all_preorders(n: int):
    """All labeled reflexive transitive relations, hence all finite topologies."""
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for code in range(1 << len(pairs)):
        rows = [1 << i for i in range(n)]
        for k, (i, j) in enumerate(pairs):
            if code >> k & 1:
                rows[i] |= 1 << j
        if all(not (rows[i] >> j & 1) or rows[j] & ~rows[i] == 0
               for i in range(n) for j in range(n)):
            yield tuple(rows)


def topology_data(rows: tuple[int, ...]):
    n = len(rows)
    full = (1 << n) - 1
    closure = tuple(sum(1 << i for i in range(n) if rows[i] & mask)
                    for mask in range(full + 1))
    opens = tuple(mask for mask in range(full + 1)
                  if all(not (mask >> i & 1) or rows[i] & ~mask == 0
                         for i in range(n)))
    return closure, opens


def direct_tree_optima(opens: tuple[int, ...], colors: Word):
    """Independent minimax: no closure, word, or subsequence calculation."""
    @lru_cache(maxsize=None)
    def visit(mask: int) -> tuple[int, int]:
        seen = {colors[i] for i in range(len(colors)) if mask >> i & 1}
        if len(seen) <= 1:
            return (0, int(bool(mask)))
        best_depth = best_leaves = INF
        for u in opens:
            yes, no = mask & u, mask & ~u
            if yes and no:
                dy, ly = visit(yes)
                dn, ln = visit(no)
                best_depth = min(best_depth, 1 + max(dy, dn))
                best_leaves = min(best_leaves, ly + ln)
        return min(INF, best_depth), min(INF, best_leaves)
    return visit((1 << len(colors)) - 1)


def finite_topology_checks(max_n: int, q: int) -> dict:
    counts = []
    total_word_tests = 0
    tested_profiles: set[tuple[Word, ...]] = set()
    separation_tests = 0
    failure_certificates = 0
    for n in range(1, max_n + 1):
        patterns = tuple(w for k in range(1, n + 2)
                         for w in reduced_words(q, k))
        candidates = tuple(w for k in range(1, n + 1)
                           for w in product(range(q), repeat=k))
        contain = [sum(1 << j for j, v in enumerate(patterns)
                       if is_subsequence(v, w)) for w in candidates]
        trunc = [sum(1 << j for j, v in enumerate(patterns) if len(v) <= k)
                 for k in range(n + 2)]
        preorder_count = coloring_count = finite_count = 0
        for rows in all_preorders(n):
            preorder_count += 1
            closure, opens = topology_data(rows)
            full = (1 << n) - 1
            for colors in product(range(q), repeat=n):
                coloring_count += 1
                color_masks = tuple(sum(1 << i for i, b in enumerate(colors) if b == a)
                                    for a in range(q))
                sig_bits = 0
                for j, v in enumerate(patterns):
                    f = full
                    for a in reversed(v):
                        f = closure[f & color_masks[a]]
                    if f:
                        sig_bits |= 1 << j
                separable = all(colors[i] == colors[j]
                                for i in range(n) for j in range(n)
                                if rows[i] >> j & 1 and rows[j] >> i & 1)
                assert separable == (sig_bits & ~trunc[n] == 0)
                d, leaves = direct_tree_optima(opens, colors)
                if separable:
                    finite_count += 1
                    sig = tuple(v for j, v in enumerate(patterns) if sig_bits >> j & 1)
                    basis = maximal_basis(sig)
                    master = shortest_supersequence(basis, q)
                    assert leaves == len(master)
                    assert d == (len(master) - 1).bit_length()
                    if basis not in tested_profiles:
                        tested_profiles.add(basis)
                        for v in patterns:
                            if v not in sig:
                                separating_word(basis, v)
                                separation_tests += 1
                else:
                    assert d == INF and leaves == INF
                for w, contained in zip(candidates, contain):
                    f = full
                    for a in reversed(w):
                        f = closure[f & ~color_masks[a]]
                    accepted = f == 0
                    assert accepted == (sig_bits & ~contained == 0)
                    short_obstructions = sig_bits & trunc[len(w)] & ~contained
                    assert accepted == (short_obstructions == 0)
                    if not accepted:
                        j = (short_obstructions & -short_obstructions).bit_length() - 1
                        assert len(patterns[j]) <= len(w)
                        failure_certificates += 1
                    total_word_tests += 1
        counts.append({"points": n, "labeled_topologies": preorder_count,
                       "colorings": coloring_count,
                       "finite_tree_colorings": finite_count})
    return {"alphabet_size": q, "counts": counts,
            "word_admissibility_comparisons": total_word_tests,
            "short_failure_certificates": failure_certificates,
            "distinct_finite_signatures": len(tested_profiles),
            "separation_word_tests": separation_tests,
            "all_passed": True}


def universal_word(q: int, r: int) -> Word:
    return tuple(i % q for i in range((q - 1) * r + 1))


def extremal_checks() -> dict:
    cases = []
    for q, maximum_r in ((2, 8), (3, 6), (4, 3)):
        for r in range(1, maximum_r + 1):
            constraints = tuple(reduced_words(q, r))
            w = universal_word(q, r)
            assert all(is_subsequence(v, w) for v in constraints)
            tested = 0
            for candidate in reduced_words(q, len(w) - 1):
                assert any(not is_subsequence(v, candidate) for v in constraints)
                tested += 1
            cases.append({"q": q, "rank": r, "basis_size": len(constraints),
                          "optimal_layers": len(w), "word": list(w),
                          "one_shorter_candidates_rejected": tested})
    hard = tuple(reduced_words(3, 4))
    soft_rank_words = tuple((w[0],) + w[:-1] for w in hard)
    soft = maximal_basis(tuple(reduce_word(w) for w in soft_rank_words))
    assert set(soft) == set(reduced_words(3, 3))
    return {"universal_cases": cases,
            "matched_height_example": {
                "components": 24, "component_height": 4,
                "hard_rank_words": [list(w) for w in hard],
                "soft_rank_words": [list(w) for w in soft_rank_words],
                "hard_basis_size": 24, "soft_basis_size": 12,
                "hard_layers": 9, "soft_layers": 7,
                "hard_depth": 4, "soft_depth": 3,
                "agreement_through_pattern_length": 3},
            "all_passed": True}


def product_checks() -> dict:
    """Direct product topologies versus the rectangular-closure formula."""
    factors = []
    for n in (1, 2):
        for rows in all_preorders(n):
            closure, _ = topology_data(rows)
            for colors in product(range(2), repeat=n):
                if not all(colors[i] == colors[j] for i in range(n) for j in range(n)
                           if rows[i] >> j & 1 and rows[j] >> i & 1):
                    continue
                def occurrence(w, cl=closure, col=colors, size=n):
                    f = (1 << size) - 1
                    for a in reversed(w):
                        f = cl[f & sum(1 << i for i, b in enumerate(col) if b == a)]
                    return f
                rank = max(k for k in range(1, n + 1)
                           if any(occurrence(w) for w in reduced_words(2, k)))
                factors.append((rows, colors, rank, occurrence))
    pairs = word_tests = 0
    for rx, cx, rankx, occx in factors:
        for ry, cy, ranky, occy in factors:
            nx, ny = len(rx), len(ry)
            rows = tuple(sum(1 << (ii * ny + jj)
                             for ii in range(nx) for jj in range(ny)
                             if rx[i] >> ii & 1 and ry[j] >> jj & 1)
                         for i in range(nx) for j in range(ny))
            colors = tuple(2 * a + b for a in cx for b in cy)
            closure, opens = topology_data(rows)
            rank = 0
            for k in range(1, rankx + ranky + 1):
                for w in reduced_words(4, k):
                    f = (1 << (nx * ny)) - 1
                    for a in reversed(w):
                        f = closure[f & sum(1 << i for i, b in enumerate(colors) if a == b)]
                    fx = occx(tuple(a // 2 for a in w))
                    fy = occy(tuple(a % 2 for a in w))
                    rectangular = sum(1 << (i * ny + j) for i in range(nx) for j in range(ny)
                                      if fx >> i & 1 and fy >> j & 1)
                    assert f == rectangular
                    if f:
                        rank = max(rank, k)
                    word_tests += 1
            assert rank == rankx + ranky - 1
            dx, lx = direct_tree_optima(topology_data(rx)[1], cx)
            dy, ly = direct_tree_optima(topology_data(ry)[1], cy)
            dp, lp = direct_tree_optima(opens, colors)
            assert max(dx, dy) <= dp <= dx + dy
            assert max(lx, ly) <= lp <= lx * ly
            pairs += 1
    return {"factor_colorings": len(factors), "product_pairs": pairs,
            "rectangular_closure_tests": word_tests, "all_passed": True}


def graph_checks() -> dict:
    cases = 0
    for q in range(1, 5):
        pairs = tuple((a, b) for a in range(q) for b in range(q) if a != b)
        for mask in range(1 << len(pairs)):
            edges = tuple(e for i, e in enumerate(pairs) if mask >> i & 1)
            largest = 0
            for subset in range(1 << q):
                remaining = {v for v in range(q) if subset >> v & 1}
                size = len(remaining)
                while remaining:
                    sources = {v for v in remaining
                               if not any(a in remaining and b == v for a, b in edges)}
                    if not sources:
                        break
                    remaining -= sources
                if not remaining:
                    largest = max(largest, size)
            basis = maximal_basis(tuple((a,) for a in range(q)) + edges)
            master = shortest_supersequence(basis, q)
            assert len(master) == 2 * q - largest
            cases += 1
    return {"all_loopless_digraphs_through_vertices": 4,
            "digraphs_checked": cases, "all_passed": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=4, choices=range(1, 5))
    parser.add_argument("--q", type=int, default=3, choices=range(2, 5))
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "verification.json")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Do not run with -O: assertions are verification conditions")
    start = time.perf_counter()
    result = {"python": platform.python_version(),
              "finite_topologies": finite_topology_checks(args.max_n, args.q),
              "extremal": extremal_checks(),
              "products": product_checks(),
              "rank_one_graphs": graph_checks(),
              "scope": "Exact finite checks only; infinite-space results rely on written proofs."}
    result["elapsed_seconds"] = round(time.perf_counter() - start, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "extremal"}, indent=2))
    print(f"All checks passed. Full record: {args.output}")

if __name__ == "__main__":
    main()
