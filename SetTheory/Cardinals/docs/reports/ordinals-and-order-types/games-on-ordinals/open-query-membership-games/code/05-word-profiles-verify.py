#!/usr/bin/env python3
"""Finite checks for Universal Word Profiles on Scattered Spaces.

Python 3.10+, standard library only. These tests do not model a Hausdorff
convergent sequence or prove any infinite-space statement. Run without -O.
Output is written only under the supplied --output directory.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
import time
from functools import lru_cache
from pathlib import Path
from typing import Iterator, Sequence

Word = tuple[int, ...]


def reduced_words(q: int, n: int) -> Iterator[Word]:
    if n == 0:
        yield ()
        return
    for prefix in reduced_words(q, n - 1):
        for a in range(q):
            if not prefix or prefix[-1] != a:
                yield prefix + (a,)


def embeds(pattern: Sequence[int], word: Sequence[int]) -> bool:
    """Direct subsequence scan, independent of the envelope test."""
    j = 0
    for a in word:
        if j < len(pattern) and a == pattern[j]:
            j += 1
    return j == len(pattern)


def embedding(pattern: Sequence[int], word: Sequence[int]) -> list[int]:
    result: list[int] = []
    j = 0
    for a in pattern:
        while j < len(word) and word[j] != a:
            j += 1
        if j == len(word):
            raise ValueError("Pattern is not a subsequence")
        result.append(j)
        j += 1
    return result


def envelope(word: Word, q: int, h: int, starts: Sequence[int]) -> list[int] | None:
    """Inclusive next-position recurrence, with zero-based indices."""
    if not word:
        return None
    n = len(word)
    next_at = [[n] * q for _ in range(n + 1)]
    for j in range(n - 1, -1, -1):
        next_at[j] = next_at[j + 1].copy()
        next_at[j][word[j]] = j
    b = max(next_at[0][a] for a in starts)
    if b == n:
        return None
    bounds = [b]
    for _ in range(h):
        b = max(next_at[b])
        if b == n:
            return None
        bounds.append(b)
    return bounds


def ceil_log2(n: int) -> int:
    if n <= 0:
        raise ValueError("Positive argument required")
    return (n - 1).bit_length()


def layers(h: int, t: int | None, q: int) -> int:
    if h < 0 or q < 1 or (t is not None and t < 1):
        raise ValueError("Invalid height, cardinality, or alphabet")
    return h * (q - 1) + (q if t is None else min(q, t))


def depth(h: int, t: int | None, q: int) -> int:
    return ceil_log2(layers(h, t, q))


def threshold(h: int, t: int, d: int) -> int:
    if h < 1 or t < 1 or d < 0:
        raise ValueError("Threshold needs positive normalized height/cardinality")
    b = 1 << d
    return max((b + h) // (h + 1), (b + h - t) // h)


def normalize(h: int, t: int | None) -> tuple[int, int]:
    if h < 0 or (t is not None and t < 1):
        raise ValueError("Height must be nonnegative and terminal size positive")
    return (h + 1, 1) if t is None else (h, t)


def eventual_period(h: int) -> tuple[int, int]:
    if h < 1:
        raise ValueError("Positive normalized height required")
    p = 0
    odd = h
    while odd % 2 == 0:
        odd //= 2
        p += 1
    if odd == 1:
        return p, 1
    residue = 2 % odd
    period = 1
    while residue != 1:
        residue = residue * 2 % odd
        period += 1
    return p, period


def spectra_equal(h: int, t: int | None, k: int, u: int | None) -> bool:
    """Exact all-alphabet query-spectrum test proved in the article."""
    h, t = normalize(h, t)
    k, u = normalize(k, u)
    if h == 0 or k == 0:
        return h == k == 0 and ceil_log2(t) == ceil_log2(u)
    if h != k:
        return False
    p, period = eventual_period(h)
    d0 = p
    bound = (h + 1) * max(t, u) - h
    while (1 << d0) < bound:
        d0 += 1
    return all(threshold(h, t, d) == threshold(h, u, d)
               for d in range(d0 + period))


def forest(q: int, h: int, s: int) -> tuple[list[int], list[int]]:
    """Finite ancestor poset, NOT a finite Hausdorff topological model."""
    colors: list[int] = []
    parent: list[int] = []

    def add(a: int, r: int, p: int) -> None:
        v = len(colors)
        colors.append(a)
        parent.append(p)
        if r:
            for b in range(q):
                if b != a:
                    add(b, r - 1, v)
    for a in range(s):
        add(a, h, -1)
    return colors, parent


def minimax(colors: list[int], parent: list[int]) -> tuple[int, int, int]:
    n = len(colors)
    full = (1 << n) - 1
    opens = []
    for mask in range(1 << n):
        if all(p == -1 or not(mask >> p & 1) or (mask >> v & 1)
               for v, p in enumerate(parent)):
            opens.append(mask)

    @lru_cache(None)
    def solve(mask: int) -> tuple[int, int]:
        labels = {colors[v] for v in range(n) if mask >> v & 1}
        if len(labels) <= 1:
            return (0, 1)
        best_depth = n + 1
        best_leaves = n + 1
        for u in opens:
            yes = mask & u
            no = mask & (full ^ u)
            if not yes or not no:
                continue
            dy, ly = solve(yes)
            dn, ln = solve(no)
            best_depth = min(best_depth, 1 + max(dy, dn))
            best_leaves = min(best_leaves, ly + ln)
        if best_depth == n + 1:
            raise AssertionError("Finite poset coloring unexpectedly unsolvable")
        return best_depth, best_leaves

    d, l = solve(full)
    return d, l, len(opens)


def balanced_tree(word: Word, lo: int = 0, hi: int | None = None) -> dict:
    hi = len(word) if hi is None else hi
    if hi - lo == 1:
        return {"position": lo, "color": word[lo]}
    mid = (lo + hi) // 2
    return {"ask_suffix_from_position": mid,
            "no": balanced_tree(word, lo, mid),
            "yes": balanced_tree(word, mid, hi)}


def route(tree: dict, position: int) -> tuple[int, int]:
    count = 0
    while "position" not in tree:
        count += 1
        tree = tree["yes" if position >= tree["ask_suffix_from_position"] else "no"]
    return tree["color"], count


def check_universal() -> dict:
    checks = 0
    rows = []
    configs = [(q, h, s) for q, max_h in [(2, 5), (3, 3), (4, 2)]
               for h in range(max_h + 1) for s in range(1, q + 1)]
    for q, h, s in configs:
        required = tuple(w for w in reduced_words(q, h + 1) if w[0] < s)
        expected = h * (q - 1) + s
        minimum = None
        local = 0
        # Reduced candidates suffice for minimum length; separate tests below
        # include unreduced candidates to audit inclusive next-position behavior.
        for n in range(expected + 1):
            for word in reduced_words(q, n):
                explicit = all(embeds(p, word) for p in required)
                fast = envelope(word, q, h, range(s)) is not None
                assert explicit == fast, (q, h, s, word)
                if explicit and minimum is None:
                    minimum = n
                checks += 1
                local += 1
        assert minimum == expected, (q, h, s, minimum, expected)
        cyclic = tuple(i % q for i in range(expected))
        assert all(embeds(p, cyclic) for p in required)
        rows.append({"q": q, "h": h, "s": s, "patterns": len(required),
                     "candidate_words": local, "minimum": minimum})
    repeated_checks = 0
    for q in (2, 3):
        for n in range(7):
            for word in itertools.product(range(q), repeat=n):
                for h in range(3):
                    for s in range(1, q + 1):
                        explicit = all(embeds(p, word)
                                       for p in reduced_words(q, h + 1) if p[0] < s)
                        assert explicit == (envelope(word, q, h, range(s)) is not None)
                        repeated_checks += 1
    return {"configurations": len(configs), "reduced_candidate_checks": checks,
            "unrestricted_candidate_checks": repeated_checks, "rows": rows}


def check_forests() -> list[dict]:
    rows = []
    for q in range(2, 5):
        for h in range(5):
            for s in range(1, q + 1):
                colors, parents = forest(q, h, s)
                if len(colors) > 10:
                    continue
                d, l, opens = minimax(colors, parents)
                expected = h * (q - 1) + s
                assert l == expected
                assert d == ceil_log2(expected)
                rows.append({"q": q, "h": h, "s": s, "points": len(colors),
                             "open_sets": opens, "leaves": l, "depth": d})
    return rows


def check_spectra() -> dict:
    boundary_checks = 0
    for h in range(1, 25):
        for t in range(1, 65):
            for d in range(13):
                q = threshold(h, t, d)
                assert q >= 1
                assert layers(h, t, q) <= 1 << d
                assert layers(h, t, q + 1) > 1 << d
                boundary_checks += 1
    aliases: dict[str, list[list[int]]] = {}
    equivalence_checks = 0
    for h in range(1, 17):
        groups: list[list[int]] = []
        for t in range(1, 33):
            for group in groups:
                if spectra_equal(h, t, h, group[0]):
                    group.append(t)
                    break
            else:
                groups.append([t])
        aliases[str(h)] = groups
        for t in range(1, 33):
            for u in range(t, 33):
                exact = spectra_equal(h, t, h, u)
                long_test = all(threshold(h, t, d) == threshold(h, u, d)
                                for d in range(101))
                assert exact == long_test, (h, t, u)
                # A positive equivalence is additionally tested from the direct
                # depth definition, not only via the threshold formula.
                if exact:
                    assert all(depth(h, t, q) == depth(h, u, q)
                               for q in range(1, 257))
                equivalence_checks += 1
    dyadic_checks = 0
    for r in range(6):
        h = 1 << r
        for t in range(1, h + 1):
            for q in range(2, 1025):
                assert depth(h, t, q) == r + ceil_log2(q)
                dyadic_checks += 1
    normalization_checks = 0
    for h in range(17):
        for q in range(1, 257):
            assert layers(h, None, q) == layers(h + 1, 1, q)
            assert spectra_equal(h, None, h + 1, 1)
            normalization_checks += 1
    return {"threshold_boundary_cases": boundary_checks,
            "spectrum_pair_cases": equivalence_checks,
            "dyadic_alias_cases": dyadic_checks,
            "infinite_top_normalization_cases": normalization_checks,
            "alias_classes_for_T_1_to_32": aliases}


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without -O: assertions are verification conditions")
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    universal = check_universal()
    finite_forests = check_forests()
    spectra = check_spectra()
    q, h, s = 3, 2, 1
    word = (0, 1, 2, 0, 1)
    patterns = [w for w in reduced_words(q, h + 1) if w[0] < s]
    tree = balanced_tree(word)
    for j, a in enumerate(word):
        got, moves = route(tree, j)
        assert got == a and moves <= ceil_log2(len(word))
    certificate = {"q": q, "h": h, "starts": [0], "word": word,
                   "zero_based_envelope": envelope(word, q, h, [0]),
                   "embeddings": [{"pattern": p, "positions": embedding(p, word)}
                                  for p in patterns], "query_tree": tree}
    sample_rows = [{"h": h, "t": "infinite" if t is None else t,
                    "q": q, "layers": layers(h, t, q), "depth": depth(h, t, q)}
                   for h in range(7) for t in (1, 2, 3, None) for q in range(2, 9)]
    summary = {"status": "all assertions passed", "python": platform.python_version(),
               "elapsed_seconds": round(time.perf_counter() - start, 3),
               "universal": {k: v for k, v in universal.items() if k != "rows"},
               "finite_forest_cases": len(finite_forests),
               "spectra": {k: v for k, v in spectra.items()
                           if k != "alias_classes_for_T_1_to_32"},
               "scope": "Finite evidence only; infinite topological results rely on written proofs."}
    for name, obj in [("verification.json", summary), ("certificate.json", certificate),
                      ("depth_aliases.json", spectra["alias_classes_for_T_1_to_32"])]:
        (args.output / name).write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")
    write_csv(args.output / "universal_words.csv", universal["rows"])
    write_csv(args.output / "finite_forests.csv", finite_forests)
    write_csv(args.output / "sample_spectra.csv", sample_rows)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
