#!/usr/bin/env python3
"""Exact, dependency-free certificates for ordinal_product_coherence.tex.

This is not a formal proof assistant.  The article supplies the proofs for
arbitrary monoids, linear orders, and all k.  Here we check finite instances,
a finite certificate covering depth-two evaluations of F_4, and a symbolic
ultimately-periodic omega-word witness (not a finite truncation).

Run: python3 verify.py [--output verification_results.json]
Python 3.9 or later; no third-party dependencies.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, FrozenSet, List, Optional, Sequence, Set, Tuple, Union


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def xor(values: Sequence[int]) -> int:
    result = 0
    for value in values:
        require(value in (0, 1), "C2 value must be 0 or 1")
        result ^= value
    return result


def check_finite_c2(max_length: int = 10) -> Dict[str, int]:
    words = 1  # empty word, checked separately
    checks = 1
    require(xor(()) == 0, "empty product")
    for length in range(1, max_length + 1):
        for word in itertools.product((0, 1), repeat=length):
            words += 1
            value = xor(word)
            for cut_mask in range(1 << (length - 1)):
                block_values = []
                start = 0
                for cut in range(1, length):
                    if cut_mask & (1 << (cut - 1)):
                        block_values.append(xor(word[start:cut]))
                        start = cut
                block_values.append(xor(word[start:]))
                require(xor(block_values) == value, "finite C2 regrouping")
                checks += 1
    return {"maximum_word_length": max_length, "words_including_empty": words,
            "convex_partition_checks_including_empty": checks}


@dataclass(frozen=True)
class Leaf:
    value: int


@dataclass(frozen=True)
class Finite:
    children: Tuple["Tree", ...]


@dataclass(frozen=True)
class OmegaRepeat:
    # Repeat this finite, nonempty pattern of children omega times.
    pattern: Tuple["Tree", ...]


Tree = Union[Leaf, Finite, OmegaRepeat]


@dataclass(frozen=True)
class Word:
    prefix: Tuple[int, ...]
    period: Optional[Tuple[int, ...]] = None

    def at(self, index: int) -> int:
        if index < len(self.prefix):
            return self.prefix[index]
        if self.period is None:
            raise IndexError(index)
        return self.period[(index - len(self.prefix)) % len(self.period)]


def evaluate_tree(tree: Tree) -> Tuple[int, int, Word]:
    if isinstance(tree, Leaf):
        return tree.value, 0, Word((tree.value,))
    children = tree.children if isinstance(tree, Finite) else tree.pattern
    require(bool(children), "Witness trees have no empty nodes")
    results = [evaluate_tree(child) for child in children]
    height = 1 + max(result[1] for result in results)
    if isinstance(tree, OmegaRepeat):
        require(all(result[0] == 0 for result in results),
                "Only all-identity infinite node products are prescribed")
        require(all(result[2].period is None for result in results),
                "Symbolic witness only repeats finite flattened blocks")
        period = tuple(value for result in results for value in result[2].prefix)
        require(bool(period), "omega period must be nonempty")
        return 0, height, Word((), period)
    prefix: Tuple[int, ...] = ()
    period: Optional[Tuple[int, ...]] = None
    for result in results:
        require(period is None, "Symbolic witness permits only a final omega summand")
        prefix += result[2].prefix
        period = result[2].period
    return xor([result[0] for result in results]), height, Word(prefix, period)


def equal_omega_words(first: Word, second: Word) -> Tuple[bool, int]:
    require(first.period is not None and second.period is not None,
            "Both words must have order type omega")
    # After both finite prefixes, the pair of letters is periodic with this lcm.
    lcm = len(first.period) * len(second.period) // math.gcd(
        len(first.period), len(second.period))
    bound = max(len(first.prefix), len(second.prefix)) + lcm
    return all(first.at(i) == second.at(i) for i in range(bound)), bound


def check_omega_witness() -> Dict[str, Any]:
    a = Leaf(1)
    even = OmegaRepeat((Finite((a, a)),))
    shifted = Finite((a, even))
    v_even, h_even, w_even = evaluate_tree(even)
    v_shift, h_shift, w_shift = evaluate_tree(shifted)
    same, bound = equal_omega_words(w_even, w_shift)
    require(same and v_even == 0 and v_shift == 1, "omega contradiction")
    require((h_even, h_shift) == (2, 3), "witness depths")
    return {
        "alphabet": {"0": "e", "1": "a"},
        "even_pairs": {"height": h_even, "value": v_even,
                       "prefix": w_even.prefix, "period": w_even.period},
        "shifted_pairs": {"height": h_shift, "value": v_shift,
                          "prefix": w_shift.prefix, "period": w_shift.period},
        "flattened_omega_words_equal": same,
        "exact_periodicity_comparison_bound": bound,
        "method": "finite-prefix plus least-common-multiple period certificate"
    }


def associative(table: Sequence[Sequence[int]]) -> bool:
    n = len(table)
    return all(table[table[a][b]][c] == table[a][table[b][c]]
               for a in range(n) for b in range(n) for c in range(n))


def check_monoids(max_size: int = 4) -> List[Dict[str, int]]:
    rows = []
    for n in range(1, max_size + 1):
        positions = [(a, b) for a in range(1, n) for b in range(1, n)]
        candidates = monoids = conical_count = obstructed_count = extensions = 0
        for entries in itertools.product(range(n), repeat=len(positions)):
            candidates += 1
            table = [[0] * n for _ in range(n)]
            for a in range(n):
                table[0][a] = a
                table[a][0] = a
            for (a, b), value in zip(positions, entries):
                table[a][b] = value
            if not associative(table):
                continue
            monoids += 1
            directly_finite = all(table[b][a] == 0 for a in range(n)
                                  for b in range(n) if table[a][b] == 0)
            units = {a for a in range(n) if any(
                table[a][b] == 0 and table[b][a] == 0 for b in range(n))}
            conical = all(a == 0 and b == 0 for a in range(n)
                          for b in range(n) if table[a][b] == 0)
            require(directly_finite, "finite monoid must be directly finite")
            require(conical == (units == {0}), "classification equivalence")
            if conical:
                conical_count += 1
                # The finite restriction of the one-new-element construction.
                ext = [row + [n] for row in table] + [[n] * (n + 1)]
                require(associative(ext), "adjoined absorbing element associativity")
                require(all(ext[0][a] == a and ext[a][0] == a
                            for a in range(n + 1)), "extended identity")
                require(all((ext[a][b] != 0) == (a != 0 or b != 0)
                            for a in range(n + 1) for b in range(n + 1)),
                        "nonidentity support cannot disappear")
                extensions += 1
            else:
                obstructed_count += 1
                require(any(a != 0 for a in units), "nontrivial unit witness")
        rows.append({"size": n, "candidate_tables_identity_0": candidates,
                     "labeled_monoids_identity_0": monoids,
                     "conical_trivial_unit_group": conical_count,
                     "nontrivial_unit_group": obstructed_count,
                     "finite_extension_tables_checked": extensions})
    require([row["labeled_monoids_identity_0"] for row in rows] ==
            [1, 2, 11, 156][:max_size], "enumeration regression counts")
    return rows


def fork(k: int) -> Tuple[List[str], Dict[Tuple[str, str], str], Dict[str, FrozenSet[int]]]:
    require(k >= 3, "k must be at least 3")
    atoms = [f"a{i}" for i in range(1, k + 1)]
    left = {1: "a1", **{i: f"L{i}" for i in range(2, k + 1)}}
    right = {k: f"a{k}", **{i: f"R{i}" for i in range(1, k)}}
    symbols = atoms + [left[i] for i in range(2, k + 1)] + [right[i] for i in range(1, k)]
    rules = {(left[i - 1], f"a{i}"): left[i] for i in range(2, k + 1)}
    rules.update({(f"a{i}", right[i + 1]): right[i] for i in range(1, k)})
    require(len(rules) == 2 * k - 2, "cross products must have distinct inputs")
    intervals: Dict[str, FrozenSet[int]] = {
        f"a{i}": frozenset((i,)) for i in range(1, k + 1)}
    intervals.update({left[i]: frozenset(range(1, i + 1)) for i in range(2, k + 1)})
    intervals.update({right[i]: frozenset(range(i, k + 1)) for i in range(1, k)})
    return symbols, rules, intervals


def check_forks(max_k: int = 16) -> List[Dict[str, Any]]:
    rows = []
    for k in range(3, max_k + 1):
        symbols, rules, intervals = fork(k)
        x, y = f"L{k}", "R1"
        require(len(symbols) == 3 * k - 2, "fork cardinality")
        for (p, q), s in rules.items():
            require(intervals[p] | intervals[q] == intervals[s], "interval union invariant")
        collisions = [(s, t) for pos, s in enumerate(symbols) for t in symbols[pos + 1:]
                      if intervals[s] == intervals[t]]
        require(collisions == [(x, y)], "unique output-label interval collision")
        descendants = {s: {s} for s in symbols}
        changed = True
        while changed:
            changed = False
            for (p, q), s in rules.items():
                enlarged = descendants[s] | descendants[p] | descendants[q]
                if enlarged != descendants[s]:
                    descendants[s] = enlarged
                    changed = True
        atoms = {f"a{i}" for i in range(1, k + 1)}
        require(descendants[x] & descendants[y] == atoms, "common leaf alphabet")
        heights = {a: 0 for a in atoms}
        changed = True
        while changed:
            changed = False
            for (p, q), s in rules.items():
                if p in heights and q in heights:
                    height = 1 + max(heights[p], heights[q])
                    if s not in heights or height < heights[s]:
                        heights[s] = height
                        changed = True
        require(heights[x] == heights[y] == k - 1, "minimum atom-only depths")
        # Explicit finite combs: check each intermediate product and flat word.
        left_value, left_word = "a1", ["a1"]
        for i in range(2, k + 1):
            left_value = rules[(left_value, f"a{i}")]
            left_word.append(f"a{i}")
        right_value, right_word = f"a{k}", [f"a{k}"]
        for i in range(k - 1, 0, -1):
            right_value = rules[(f"a{i}", right_value)]
            right_word.insert(0, f"a{i}")
        require(left_word == right_word and left_value == x and right_value == y,
                "explicit unequal comb evaluations")
        rows.append({"k": k, "size": len(symbols), "coherent_through_depth": k - 2,
                     "first_conflict_depth": k - 1,
                     "conflicting_values": [x, y], "flat_word": left_word})
    return rows


def depth_two_content_certificate() -> Dict[str, Any]:
    symbols, rules, _ = fork(4)
    aliases = {"a1": "a", "a2": "b", "a3": "c", "a4": "d", "L2": "u",
               "L3": "v", "L4": "x", "R3": "w", "R2": "t", "R1": "y"}
    symbols = [aliases[s] for s in symbols]
    rules = {(aliases[p], aliases[q]): aliases[s] for (p, q), s in rules.items()}
    primitive: Dict[str, Set[FrozenSet[str]]] = {s: {frozenset((s,))} for s in symbols}
    for (p, q), s in rules.items():
        primitive[s].add(frozenset((p, q)))
    families: Dict[str, Set[FrozenSet[str]]] = {s: set() for s in symbols}
    for s in symbols:
        choices = list(primitive[s])
        # Constant outer products may have infinitely many children, but only
        # these finitely many primitive content types can occur among them.
        for mask in range(1, 1 << len(choices)):
            content: FrozenSet[str] = frozenset()
            for i, choice in enumerate(choices):
                if mask & (1 << i):
                    content = content | choice
            families[s].add(content)
    for (p, q), s in rules.items():
        for content_p in primitive[p]:
            for content_q in primitive[q]:
                families[s].add(content_p | content_q)
    owner: Dict[FrozenSet[str], str] = {}
    for s, contents in families.items():
        for content in contents:
            require(content not in owner or owner[content] == s,
                    "depth-two content family collision")
            owner[content] = s
    order = ["a", "b", "c", "d", "u", "v", "w", "t", "x", "y"]
    serialized = {s: sorted((sorted(c) for c in families[s]), key=lambda c: (len(c), c))
                  for s in order}
    return {"cross_products": {p + " " + q: s for (p, q), s in rules.items()},
            "content_families": serialized, "distinct_contents": len(owner),
            "families_pairwise_disjoint": True,
            "scope": "all depth <= 2 trees, including arbitrary linear-order branching"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    results = {
        "report": "Pairwise coherence and completion of ordinal-indexed products",
        "status": "All implemented exact checks passed",
        "scope_warning": "Computational certificates supplement, not replace, the article's proofs.",
        "finite_c2": check_finite_c2(),
        "omega_witness": check_omega_witness(),
        "finite_monoids": check_monoids(),
        "forks": check_forks(),
        "F4_depth_two_certificate": depth_two_content_certificate(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(results["status"])
    print(json.dumps({key: results[key] for key in
                      ("finite_c2", "omega_witness", "finite_monoids")}, indent=2))
    print(f"Fork parameters checked: 3 through {results['forks'][-1]['k']}")
    print(f"F4 depth-two distinct contents: {results['F4_depth_two_certificate']['distinct_contents']}")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
