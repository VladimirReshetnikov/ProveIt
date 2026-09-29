#!/usr/bin/env python3
"""Regenerate counts and reproducible checks. This is NOT a formal proof.

Usage: python code/verify.py --out data
"""
from __future__ import annotations
import argparse
import csv
import itertools
import json
import platform
import random
from pathlib import Path
from atoms import AtomPoset, FinitePoset, indices
from omega_words import Block, Word, period, embeds, separated


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def finite_words(n: int, bound: int):
    return [w for k in range(bound + 1) for w in itertools.product(range(n), repeat=k)]


def brute_ideals(a: AtomPoset) -> int:
    n = len(a.atoms)
    if n > 20:
        raise ValueError("Brute-force verification deliberately limited to 20 atoms.")
    down = [sum(1 << j for j in range(n) if a.le(j, i)) for i in range(n)]
    return sum(all(not (down[i] & ~mask) for i in indices(mask))
               for mask in range(1 << n))


def validate_atoms(a: AtomPoset) -> None:
    matrix = a.matrix()
    FinitePoset(tuple(map(str, range(len(a.atoms)))), matrix)
    for i, x in enumerate(a.atoms):
        for j, y in enumerate(a.atoms):
            require(not matrix[i][j] or x.height <= y.height, "Height monotonicity")
        if x.children:
            require(x.height == 1 + max(a.atoms[j].height for j in x.children),
                    "Incorrect node height")
            for p, q in itertools.combinations(x.children, 2):
                require(not a.le(p, q) and not a.le(q, p), "Children not antichain")


def all_small_posets():
    for n in range(4):
        edges = [(i, j) for i in range(n) for j in range(n) if i != j]
        for mask in range(1 << len(edges)):
            rel = [[i == j for j in range(n)] for i in range(n)]
            for q, (i, j) in enumerate(edges):
                if mask & (1 << q):
                    rel[i][j] = True
            try:
                yield FinitePoset(tuple(map(str, range(n))), tuple(map(tuple, rel)))
            except ValueError:
                continue


def table_checks(out: Path, stats: dict) -> None:
    cases = [
        ("A2", FinitePoset.antichain(2), [2, 5, 11, 28, 136]),
        ("C2", FinitePoset.chain(2), [2, 4, 7, 12, 22, 50]),
        ("A3", FinitePoset.antichain(3), [3, 10, 43, 1962]),
        ("C3", FinitePoset.chain(3), [3, 6, 12, 28]),
    ]
    rows = []
    for name, base, expected in cases:
        a = AtomPoset(base)
        for k, number in enumerate(expected, 1):
            if k == len(expected):
                rows.append(dict(alphabet=name, k=k, N_k=number,
                                 exponent=number - 1, J="", constructed=False))
                break
            validate_atoms(a)
            require(len(a.atoms) == number, f"N mismatch: {name}, k={k}")
            j = a.count_ideals()
            direct = a.count_ideals_direct()
            require(j == direct, f"Independent ideal counts: {name}, k={k}")
            require(len(base.labels) + j - 1 == expected[k], "Next N mismatch")
            stats["independent_ideal_count_agreements"] += 1
            if len(a.atoms) <= 12:
                require(j == brute_ideals(a), "Brute force disagrees")
                stats["brute_ideal_count_agreements"] += 1
            rows.append(dict(alphabet=name, k=k, N_k=number,
                             exponent=number - 1, J=j, constructed=True))
            if k <= 3:
                (out / f"atoms_{name}_k{k}.json").write_text(
                    json.dumps(a.export(), indent=2) + "\n", encoding="utf-8")
            if k < len(expected) - 1:
                a.extend()
    with (out / "atom_counts.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    stats["count_table_rows"] = len(rows)


def exhaustive_poset_checks(stats: dict) -> None:
    for base in all_small_posets():
        stats["finite_alphabet_posets_checked"] += 1
        a = AtomPoset(base)
        for k in range(1, 4):
            validate_atoms(a)
            stats["canonical_atom_posets_checked"] += 1
            j = a.count_ideals()
            require(j == a.count_ideals_direct(), "Independent count disagreement")
            stats["independent_ideal_count_agreements"] += 1
            if len(a.atoms) <= 10:
                require(j == brute_ideals(a), "Brute count disagreement")
                stats["brute_ideal_count_agreements"] += 1
            if k < 3:
                a.extend()


def symbolic_checks(stats: dict) -> None:
    rng = random.Random(20260919)
    words = finite_words(2, 4)
    prefixes = finite_words(2, 2)
    for base in (FinitePoset.antichain(2), FinitePoset.chain(2)):
        for u in words:
            for v in words:
                fu = Word((Block(u + (1,), (0,)),))
                fv = Word((Block(v + (1,), (0,)),))
                require(embeds(fu, fv, base) == embeds(Word(tail=u), Word(tail=v), base),
                        "Marker reflection failed")
                stats["marker_pairs"] += 1
        candidates = [Word((Block(p, s),)) for p in prefixes
                      for s in ((0,), (1,), (0, 1))]
        for _ in range(5000):
            m = rng.randrange(1, 5)
            left = tuple(rng.choice(candidates) for _ in range(m))
            right = left if rng.randrange(5) == 0 else tuple(
                rng.choice(candidates) for _ in range(m))
            l = sum(left, Word())
            r = sum(right, Word())
            require(embeds(l, r, base) == all(embeds(x, y, base)
                                            for x, y in zip(left, right)),
                    "Equal-block reflection failed")
            stats["equal_block_pairs"] += 1
        phases = [(((0,),), period(1))]
        if base == FinitePoset.antichain(2):
            phases.append((((0,), (1,)), period(0, 1)))
        for allowed_cycles, z in phases:
            def old_word() -> Word:
                return Word(tuple(Block(rng.choice(prefixes), rng.choice(allowed_cycles))
                                  for _ in range(rng.randrange(1, 4))))
            for _ in range(6000):
                m = rng.randrange(4)
                count_right = m if rng.randrange(3) else rng.randrange(4)
                left = tuple(old_word() for _ in range(m + 1))
                right = left if count_right == m and rng.randrange(5) == 0 else tuple(
                    old_word() for _ in range(count_right + 1))
                require(all(x.omega_ended and not embeds(z, x, base)
                            for x in left + right), "Separator precondition failed")
                result = embeds(separated(left, z), separated(right, z), base)
                if result:
                    require(m <= count_right, "Separator count decreased")
                if m == count_right:
                    require(result == all(embeds(x, y, base) for x, y in zip(left, right)),
                            "Separator coordinate reflection failed")
                    stats["equal_separator_pairs"] += 1
                stats["separator_pairs"] += 1
        # Deliberately test absorption, which makes the naive proof invalid.
        a = period(0)
        fa = Word(tail=(0,)) + a
        require(embeds(a, fa, base) and embeds(fa, a, base), "Absorption sanity check")
        stats["absorption_checks"] += 1
    # With one letter the whole order is precisely ordinal length comparison.
    one = FinitePoset.chain(1)
    for b in range(5):
        for tail in range(5):
            w = Word(tuple(Block((), (0,)) for _ in range(b)), (0,) * tail)
            for c in range(5):
                for suffix in range(5):
                    v = Word(tuple(Block((), (0,)) for _ in range(c)), (0,) * suffix)
                    require(embeds(w, v, one) == ((b, tail) <= (c, suffix)),
                            "Singleton length-order check failed")
                    stats["singleton_pairs"] += 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    stats = {key: 0 for key in (
        "independent_ideal_count_agreements", "brute_ideal_count_agreements",
        "finite_alphabet_posets_checked", "canonical_atom_posets_checked",
        "marker_pairs", "equal_block_pairs", "separator_pairs", "equal_separator_pairs",
        "absorption_checks", "singleton_pairs")}
    table_checks(args.out, stats)
    exhaustive_poset_checks(stats)
    symbolic_checks(stats)
    result = {"status": "PASS", "seed": 20260919,
              "python": platform.python_version(), "counts": stats,
              "scope": "Exact finite combinatorics and symbolic examples; not a formal verification of the transfinite theorem."}
    (args.out / "verification.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
