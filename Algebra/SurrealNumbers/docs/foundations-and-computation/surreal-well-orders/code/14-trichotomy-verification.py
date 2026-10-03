#!/usr/bin/env python3
"""Finite diagnostics for Lexicographic Well-Orders of the Surreals II.

These tests check finite combinatorial kernels only. They do NOT prove
surreal saturation, infinite-cardinal claims, or class-theoretic results.
No third-party dependencies or network access are required.
"""
from __future__ import annotations

import itertools as it
import json
import platform
from pathlib import Path
from typing import Iterable, Sequence

Permutation = tuple[int, ...]


def require(condition: bool, message: str) -> None:
    """Assertions that remain enabled even under python -O."""
    if not condition:
        raise AssertionError(message)


def cmp(a: Sequence[int], b: Sequence[int]) -> int:
    return (a > b) - (a < b)


def subsets(n: int) -> Iterable[tuple[int, ...]]:
    for k in range(n + 1):
        yield from it.combinations(range(n), k)


def support(p: Permutation) -> set[int]:
    return {i for i, value in enumerate(p) if i != value}


def extend_partial(n: int, partial: dict[int, int]) -> Permutation:
    """Extend a finite injection, fixing outside domain union range."""
    require(len(set(partial.values())) == len(partial), "Noninjective input")
    require(all(0 <= x < n for x in (*partial, *partial.values())),
            "Input outside the finite universe")
    domain = set(partial)
    image = set(partial.values())
    carrier = domain | image
    remainder = dict(zip(sorted(carrier - domain), sorted(carrier - image)))
    result = list(range(n))
    for x, y in (partial | remainder).items():
        result[x] = y
    return tuple(result)


def check_common_prefix() -> dict[str, object]:
    pairs = 0
    for n in range(6):
        words = list(it.permutations(range(n)))
        records = {}
        for p in words:
            pos = {x: i for i, x in enumerate(p)}
            pred = {x: frozenset(p[:pos[x]]) for x in p}
            relation = frozenset((x, y) for x in p for y in p if pos[x] < pos[y])
            records[p] = (pred, relation)
        for p, q in it.product(words, repeat=2):
            pp, rp = records[p]
            pq, rq = records[q]
            common = set()
            for x in range(n):
                if pp[x] == pq[x]:
                    carrier = pp[x]
                    sp = {(a, b) for a, b in rp if a in carrier and b in carrier}
                    sq = {(a, b) for a, b in rq if a in carrier and b in carrier}
                    if sp == sq:
                        common.add(x)
            length = next((i for i in range(n) if p[i] != q[i]), n)
            require(common == set(p[:length]), "Relation/common-word prefix mismatch")
            if p == q:
                comparison = 0
            else:
                a = next(x for x in p if x not in common)
                b = next(x for x in q if x not in common)
                comparison = (a > b) - (a < b)
            require(comparison == cmp(p, q), "Relation lexical comparison mismatch")
            pairs += 1
    return {"passed": True, "max_alphabet_size": 5, "ordered_pairs": pairs}


def check_cylinders_and_crossings() -> dict[str, object]:
    cylinders_count = cuts_count = 0
    for n in range(1, 7):
        words = list(it.permutations(range(n)))
        positions: dict[tuple[int, ...], list[int]] = {}
        for i, word in enumerate(words):
            for length in range(n + 1):
                positions.setdefault(word[:length], []).append(i)
        intervals = {}
        for p, indices in positions.items():
            require(indices == list(range(indices[0], indices[-1] + 1)),
                    "Nonconvex prefix cylinder")
            intervals[p] = (indices[0], indices[-1])
            cylinders_count += 1
        # Cut k includes exactly the first k finite words.
        for k in range(1, len(words)):
            crossing = [p for p, (lo, hi) in intervals.items() if lo < k <= hi]
            require(() in crossing, "Proper cut must cross the root")
            crossing.sort(key=len)
            for shorter, longer in zip(crossing, crossing[1:]):
                require(len(shorter) < len(longer), "Two crossing prefixes at one length")
                require(longer[:len(shorter)] == shorter, "Crossing prefixes not a chain")
            lengths = {len(p) for p in crossing}
            require(lengths == set(range(max(lengths) + 1)), "Missing ancestor")
            cuts_count += 1
    return {"passed": True, "max_alphabet_size": 6,
            "cylinders": cylinders_count, "proper_finite_cuts": cuts_count,
            "scope": "Convexity and crossing-chain lemma, not the saturated trichotomy"}


def check_partial_extensions() -> dict[str, object]:
    cases = 0
    for n in range(7):
        for domain in subsets(n):
            for images in it.permutations(range(n), len(domain)):
                partial = dict(zip(domain, images))
                p = extend_partial(n, partial)
                require(sorted(p) == list(range(n)), "Extension is not a permutation")
                require(all(p[x] == y for x, y in partial.items()), "Partial map changed")
                require(support(p) <= set(domain) | set(images), "Extraneous support")
                cases += 1
    return {"passed": True, "max_alphabet_size": 6, "partial_injections": cases}


def check_support_compression() -> dict[str, object]:
    candidates = comparisons = 0
    for n in range(1, 6):
        words = list(it.permutations(range(n)))
        baselines = sorted({tuple(range(n)), tuple(reversed(range(n))),
                            tuple((i + 1) % n for i in range(n))})
        for positions in subsets(n):
            s = set(positions)
            inputs = []
            for values in it.permutations(positions):
                p = list(range(n))
                for x, y in zip(positions, values):
                    p[x] = y
                inputs.append(tuple(p))
            for q in words:
                outside = support(q) - s
                if not outside:
                    continue
                gamma = min(outside)
                partial = {i: q[i] for i in range(gamma + 1) if q[i] != i}
                r = extend_partial(n, partial)
                require(r[:gamma + 1] == q[:gamma + 1], "Prefix not retained")
                require(set(partial) <= s | {gamma}, "Compression domain bound failed")
                require(len(support(r)) <= 2 * (len(s) + 1), "Finite support bound failed")
                for b in baselines:
                    eq = tuple(b[x] for x in q)
                    er = tuple(b[x] for x in r)
                    for a in inputs:
                        ea = tuple(b[x] for x in a)
                        require(cmp(ea, eq) == cmp(ea, er),
                                "Compression changed comparison with a supported input")
                        comparisons += 1
                candidates += 1
    return {"passed": True, "max_alphabet_size": 5,
            "compressed_candidates": candidates, "comparison_checks": comparisons,
            "baselines": "Identity, reversal, and cyclic shift (duplicates removed)"}


def sign_cmp(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    for x, y in it.zip_longest(a, b, fillvalue=0):
        if x != y:
            return (x > y) - (x < y)
    return 0


def sign_code(s: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(bit for sign in s for bit in ((0, 0) if sign < 0 else (1, 1))) + (0, 1)


def is_prefix(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return len(a) <= len(b) and b[:len(a)] == a


def check_sign_and_word_codes() -> dict[str, object]:
    signs = [s for n in range(7) for s in it.product((-1, 1), repeat=n)]
    sign_pairs = word_pairs = 0
    for a, b in it.product(signs, repeat=2):
        ca, cb = sign_code(a), sign_code(b)
        require(cmp(ca, cb) == sign_cmp(a, b), "Numerical code comparison failed")
        if a != b:
            require(not is_prefix(ca, cb) and not is_prefix(cb, ca), "Not prefix-free")
        sign_pairs += 1
    from functools import cmp_to_key
    alphabet = sorted([s for n in range(3) for s in it.product((-1, 1), repeat=n)],
                      key=cmp_to_key(sign_cmp))
    words = [w for n in range(4) for w in it.product(range(len(alphabet)), repeat=n)]
    codes = {}
    for last in (False, True):
        for word in words:
            inner = tuple(bit for x in word for bit in sign_code(alphabet[x]))
            data = ((0, 0), (1, 0)) if last else ((0, 1), (1, 1))
            terminal = (1, 1) if last else (0, 0)
            encoded = tuple(bit for v in inner for bit in data[v]) + terminal
            codes[(last, word)] = encoded
        for a, b in it.product(words, repeat=2):
            # A terminal rank larger than every letter implements prefix-last.
            ka = a + (len(alphabet),) if last else a
            kb = b + (len(alphabet),) if last else b
            ca, cb = codes[(last, a)], codes[(last, b)]
            require(cmp(ca, cb) == cmp(ka, kb), "Outer word code changed order")
            if a != b:
                require(not is_prefix(ca, cb) and not is_prefix(cb, ca),
                        "Outer word codes not prefix-free")
            word_pairs += 1
    return {"passed": True, "max_sign_length": 6, "sign_pairs": sign_pairs,
            "word_alphabet_size": len(alphabet), "max_word_length": 3,
            "word_pairs_both_conventions": word_pairs}


def check_pair_orientation() -> dict[str, object]:
    comparisons = 0
    for pairs in range(1, 8):
        n = 2 * pairs
        baseline = tuple(reversed(range(n)))
        bits = list(it.product((0, 1), repeat=pairs))
        images = {}
        for word in bits:
            result = []
            for i, bit in enumerate(word):
                pair = sorted(baseline[2 * i:2 * i + 2])
                result.extend(reversed(pair) if bit else pair)
            result = tuple(result)
            require(sorted(result) == list(range(n)), "Pair code not a bijection")
            images[word] = result
        for a, b in it.product(bits, repeat=2):
            require(cmp(a, b) == cmp(images[a], images[b]), "Pair orientation reversed order")
            comparisons += 1
    return {"passed": True, "max_pairs": 7, "ordered_comparisons": comparisons}


def main() -> None:
    tests = {
        "labelled_common_prefix": check_common_prefix(),
        "cylinders_and_crossings": check_cylinders_and_crossings(),
        "partial_injection_extension": check_partial_extensions(),
        "support_compression": check_support_compression(),
        "self_delimiting_codes": check_sign_and_word_codes(),
        "pair_orientation": check_pair_orientation(),
    }
    output = {
        "all_passed": all(t["passed"] for t in tests.values()),
        "python_version": platform.python_version(),
        "scope": "Finite diagnostic kernels only; no infinite or class-level proof certification",
        "tests": tests,
    }
    path = Path(__file__).resolve().with_name("verification_results.json")
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
