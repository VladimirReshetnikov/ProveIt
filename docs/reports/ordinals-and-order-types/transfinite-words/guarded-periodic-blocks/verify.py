#!/usr/bin/env python3
"""Reproduce the exact finite symbolic checks accompanying article.tex.

No floating point arithmetic, external packages, or finite replacements for
omega are used. Tests audit finite representations of the proved abstraction;
they are not a formal verification of the transfinite mathematics.
"""
from __future__ import annotations

import argparse
import csv
import json
import random
import time
from itertools import product
from pathlib import Path

from ordinal_words import (Poset, Word, embeds, embeds_dp, normalize, tokens, words,
                           guard, encode_product, letter, omega,
                           naturally_labelled_posets, length_pair)


def require(condition: bool, context: object) -> None:
    if not condition:
        raise AssertionError(context)


def exhaustive_pair_checks(p: Poset, bound: int) -> dict:
    ws = tuple(words(tokens(p, p.ideals(nonempty=True)), bound))
    normal = {u: normalize(u) for u in ws}
    for u in ws:
        p.validate_word(u)
        require(embeds(p, u, normal[u]) and embeds(p, normal[u], u), ("normalization", u))
        require(length_pair(u) == length_pair(normal[u]), ("length", u))
    for u in ws:
        for v in ws:
            b = embeds(p, u, v)
            require(b == embeds_dp(p, u, v), ("greedy/DP", p, u, v))
            require(b == embeds(p, normal[u], normal[v]), ("normalization relation", p, u, v))
            if b and embeds(p, v, u):
                require(normal[u] == normal[v], ("canonical quotient", p, u, v))
    return {"word_count": len(ws), "ordered_pairs": len(ws) ** 2,
            "max_tokens": bound, "status": "passed"}


def random_word(rng: random.Random, alphabet: tuple, bound: int) -> Word:
    return tuple(rng.choice(alphabet) for _ in range(rng.randrange(bound + 1)))


def check_product_pair(p: Poset, family: tuple[int, ...], new: int,
                       us: tuple[Word, ...], vs: tuple[Word, ...]) -> None:
    src = encode_product(p, family, new, us)
    tgt = encode_product(p, family, new, vs)
    expected = all(embeds(p, u, v) for u, v in zip(us, vs))
    require(embeds(p, src, tgt) == expected,
            ("product lemma", p, family, new, us, vs, src, tgt, expected))
    require(embeds_dp(p, src, tgt) == expected,
            ("product lemma DP", p, family, new, us, vs))


def check_binary_products() -> dict:
    count = stages = 0
    for p in (Poset.antichain(2), Poset.chain(2)):
        # All support subfamilies: covers more than the single all-ideals route.
        ideals = p.ideals(nonempty=True)
        for mask in range(1 << len(ideals)):
            selected = tuple(d for i, d in enumerate(ideals) if mask & (1 << i))
            old: tuple[int, ...] = ()
            for d in selected:
                if d == p.full and not old:
                    continue
                stages += 1
                pool = tuple(words(tokens(p, old), 1))
                for arity in (1, 2, 3):
                    tuples = tuple(product(pool, repeat=arity))
                    for us in tuples:
                        for vs in tuples:
                            check_product_pair(p, old, d, us, vs)
                            count += 1
                old += (d,)
    return {"activation_stages": stages, "tuple_pairs": count, "status": "passed"}


def check_all_small_posets(rng: random.Random, samples: int, outdir: Path) -> dict:
    counts = {}
    rows = []
    random_count = stages = all_pairs = 0
    for n in range(1, 5):
        ps = naturally_labelled_posets(n)
        counts[str(n)] = len(ps)
        for index, p in enumerate(ps):
            ideals = p.ideals(nonempty=True)
            rows.append({"n": n, "index": index,
                         "upper_masks": ";".join(map(str, p.upper)),
                         "ideal_count_including_empty": len(ideals) + 1,
                         "omega_tower_inner_exponent": n + len(ideals) - 1 if n >= 2 else "exception: omega^2"})
            family: tuple[int, ...] = ()
            for d in ideals:
                if d == p.full and not family:
                    continue
                stages += 1
                alphabet = tokens(p, family)
                for _ in range(samples):
                    arity = rng.randrange(1, 5)
                    us = tuple(random_word(rng, alphabet, 10) for _ in range(arity))
                    vs = tuple(random_word(rng, alphabet, 10) for _ in range(arity))
                    # Include guaranteed positive cases: append arbitrary tokens.
                    if rng.randrange(3) == 0:
                        vs = tuple(u + random_word(rng, alphabet, 4) for u in us)
                    check_product_pair(p, family, d, us, vs)
                    random_count += 1
                family += (d,)
            for _ in range(samples):
                alphabet = tokens(p, ideals)
                u = random_word(rng, alphabet, 15)
                v = random_word(rng, alphabet, 15)
                require(embeds(p, u, v) == embeds_dp(p, u, v), ("random DP", p, u, v))
                require(embeds(p, u, v) == embeds(p, normalize(u), normalize(v)),
                        ("random normalization", p, u, v))
                all_pairs += 1
    require(counts == {"1": 1, "2": 2, "3": 7, "4": 40}, counts)
    with (outdir / "finite_posets.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    return {"naturally_labelled_counts": counts, "total_posets": len(rows),
            "activation_stages": stages, "random_product_pairs": random_count,
            "random_embedding_pairs": all_pairs, "status": "passed"}


def negative_controls() -> dict:
    p = Poset.antichain(2)
    # No guard: a finite component is absorbed by the new universal separator.
    u = (letter(0),)
    v: Word = ()
    full = (omega(p.full),)
    require(not embeds(p, u, v) and embeds(p, u + full, v + full), "unguarded absorption")
    # A last-letter guard does NOT repair universal support.
    a = (letter(0),)
    require(embeds(p, u + a + full, v + a + full), "finite full-support guard")
    # A containing old ideal destroys synchronization, even with outside-letter guard.
    new, old, outside = 1, 3, 1
    src_components = ((), (letter(0),))
    tgt_components = ((omega(old),), ())
    def naive(seq):
        return seq[0] + (letter(outside), omega(new)) + seq[1] + (letter(outside),)
    require(not embeds(p, src_components[1], tgt_components[1]), "negative components")
    require(embeds(p, naive(src_components), naive(tgt_components)), "containment negative control")
    return {"unguarded_absorption": "detected",
            "finite_guard_at_full_support": "detected",
            "old_support_contains_new_support": "detected"}


def check_universal_only(rng: random.Random, samples: int) -> dict:
    total = 0
    for p in (Poset.antichain(1), Poset.antichain(2), Poset.chain(3)):
        alphabet = tokens(p, (p.full,))
        for _ in range(samples):
            u, v = random_word(rng, alphabet, 12), random_word(rng, alphabet, 12)
            def form(w):
                r, _ = length_pair(w)
                last = max((i for i, x in enumerate(w) if x[0] == 1), default=-1)
                return r, w[last + 1:]
            r, uf = form(u)
            s, vf = form(v)
            expected = r < s or (r == s and embeds(p, uf, vf))
            require(embeds(p, u, v) == expected, ("universal-only", p, u, v))
            total += 1
    return {"pairs": total, "status": "passed"}


def check_fixed_lengths(rng: random.Random, samples: int) -> dict:
    total = 0
    for n in range(1, 5):
        for p in naturally_labelled_posets(n):
            ideals = p.ideals(nonempty=True)
            letters = tokens(p, ())
            for _ in range(samples):
                r, k = rng.randrange(5), rng.randrange(5)
                def build():
                    blocks = tuple(random_word(rng, letters, 6) + (omega(rng.choice(ideals)),)
                                   for _ in range(r))
                    tail = tuple(letter(rng.randrange(n)) for _ in range(k))
                    return blocks, tail, tuple(t for block in blocks for t in block) + tail
                ub, ut, u = build()
                vb, vt, v = build()
                expected = all(embeds(p, a, b) for a, b in zip(ub, vb)) and embeds(p, ut, vt)
                require(length_pair(u) == (r, k) == length_pair(v), ("fixed length generation", u, v))
                require(embeds(p, u, v) == expected, ("fixed length product", p, u, v, expected))
                total += 1
    return {"pairs": total, "status": "passed"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--samples", type=int, default=250)
    parser.add_argument("--seed", type=int, default=20260919)
    parser.add_argument("--pair-bound", type=int, default=4)
    args = parser.parse_args()
    if args.samples < 1 or not 0 <= args.pair_bound <= 5:
        parser.error("samples must be positive; pair-bound must lie in [0,5]")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    t = time.perf_counter()
    rng = random.Random(args.seed)
    result = {"scope": "exact finite symbolic expressions for transfinite words, not a formal proof",
              "seed": args.seed, "samples_per_stage": args.samples,
              "antichain_2": exhaustive_pair_checks(Poset.antichain(2), args.pair_bound),
              "chain_2": exhaustive_pair_checks(Poset.chain(2), args.pair_bound)}
    result["binary_support_families"] = check_binary_products()
    result["small_posets"] = check_all_small_posets(rng, args.samples, args.output_dir)
    result["singleton_full_support"] = check_universal_only(rng, 10 * args.samples)
    result["fixed_length_products"] = check_fixed_lengths(rng, args.samples)
    result["negative_controls"] = negative_controls()
    result["elapsed_seconds"] = round(time.perf_counter() - t, 3)
    result["status"] = "all checks passed"
    (args.output_dir / "verification_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
