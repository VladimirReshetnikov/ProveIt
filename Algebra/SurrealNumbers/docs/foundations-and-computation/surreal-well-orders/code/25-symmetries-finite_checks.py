#!/usr/bin/env python3
"""Finite regression checks for the one-point prefix-profile extension lemma.

The alphabet is Fraction (rational numbers), not a finite ordered alphabet.
All sampled words and trees are finite. No class or transfinite theorem is
claimed to be machine verified by these tests. Python standard library only.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import permutations, combinations
import json
from pathlib import Path
import random
from typing import Sequence

Word = tuple[Q, ...]


def first_difference(a: Word, b: Word) -> int:
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return i
    raise ValueError("Words must disagree before either one ends")


def profile(a: Word, b: Word) -> tuple[int, int]:
    k = first_difference(a, b)
    return k, 1 if a[k] > b[k] else -1


def fresh_between(lower: Sequence[Q], upper: Sequence[Q], used: set[Q]) -> Q:
    lo = max(lower) if lower else None
    hi = min(upper) if upper else None
    if lo is not None and hi is not None and not lo < hi:
        raise ValueError("The prescribed cut is not separated")
    if lo is None and hi is None:
        x = Q(0)
        while x in used:
            x += 1
        return x
    if lo is None:
        x = hi - 1
        while x in used:
            x -= 1
        return x
    if hi is None:
        x = lo + 1
        while x in used:
            x += 1
        return x
    # Infinitely many rational candidates; only finitely many are forbidden.
    n = 2
    x = lo + (hi - lo) / n
    while x in used:
        n += 1
        x = lo + (hi - lo) / n
    return x


def extension_prefix(source: Sequence[Word], target: Sequence[Word], d: Word) -> Word:
    """Construct the finite, maximum-attained case of the extension lemma."""
    if len(source) != len(target):
        raise ValueError("Source and target families have different lengths")
    if not source:
        return ()
    ds = [first_difference(d, a) for a in source]
    m = max(ds)
    top = [i for i, delta in enumerate(ds) if delta == m]
    r = target[top[0]][:m]
    if len(set(r)) != len(r):
        raise ValueError("The target prefix is not injective")
    lower = [target[i][m] for i in top if source[i][m] < d[m]]
    upper = [target[i][m] for i in top if d[m] < source[i][m]]
    x = fresh_between(lower, upper, set(r))
    return r + (x,)


def transplant_family(words: Sequence[Word], rng: random.Random) -> list[Word]:
    """Relabel a finite prefix tree monotonically, with fresh rational labels.

    This is an isomorphism between two finite sampled configurations, not a
    claim to have constructed a full infinite-tree automorphism.
    """
    images: dict[Word, Word] = {(): ()}
    nodes = {w[:i] for w in words for i in range(len(w) + 1)}
    for p in sorted(nodes, key=lambda p: (len(p), p)):
        children = sorted(q[-1] for q in nodes if len(q) == len(p) + 1 and q[:-1] == p)
        if not children:
            continue
        prefix = images[p]
        start = Q(rng.randint(-20, 20), rng.randint(1, 5))
        vals: list[Q] = []
        for _ in children:
            start += Q(rng.randint(1, 6), rng.randint(1, 7))
            while start in prefix:
                start += Q(1, 11)
            vals.append(start)
        for old, new in zip(children, vals):
            images[p + (old,)] = prefix + (new,)
    return [images[w] for w in words]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/finite_checks.json'))
    parser.add_argument('--seed', type=int, default=20261003)
    parser.add_argument('--trials', type=int, default=2500)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    counts: dict[str, int] = {}

    def check(kind: str, assertion: bool) -> None:
        if not assertion:
            raise AssertionError(f"Failed {kind}; seed={args.seed}")
        counts[kind] = counts.get(kind, 0) + 1

    alphabet = tuple(map(Q, range(-3, 4)))
    pool = list(permutations(alphabet, 4))
    for _ in range(args.trials):
        samples = rng.sample(pool, rng.randint(3, 10))
        source = list(samples[:-1])
        target = transplant_family(source, rng)
        d = samples[-1]
        for i, j in combinations(range(len(source)), 2):
            check('profile_preservation_in_sampled_tree', profile(source[i], source[j]) == profile(target[i], target[j]))
        r = extension_prefix(source, target, d)
        check('fresh_injective_extension_prefix', len(set(r)) == len(r))
        for a, b in zip(source, target):
            check('forward_one_point_extension', profile(d, a) == profile(r, b))
        # Exercise exactly the same lemma with the roles reversed.
        y = tuple(Q(rng.randint(-100, 100), 13) for _ in range(4))
        while len(set(y)) < 4 or y in target:
            y = tuple(Q(rng.randint(-100, 100), 13) for _ in range(4))
        s = extension_prefix(target, source, y)
        check('backward_prefix_injective', len(set(s)) == len(s))
        for a, b in zip(source, target):
            check('backward_one_point_extension', profile(s, a) == profile(y, b))
        # Prefix equivalence is the same as divergence at or after the level.
        for a, b in combinations(source, 2):
            delta = first_difference(a, b)
            for level in range(5):
                check('prefix_equivalence_from_divergence', (a[:level] == b[:level]) == (level <= delta))

    # Finite partial injections really do extend on their finite union.
    for n in range(1, 8):
        universe = tuple(range(n))
        for m in range(n + 1):
            for vals in permutations(universe, m):
                partial = dict(zip(range(m), vals))
                support_union = set(range(m)) | set(vals)
                holes_d = sorted(support_union - set(partial))
                holes_r = sorted(support_union - set(vals))
                p = dict(partial)
                p.update(zip(holes_d, holes_r))
                image = tuple(p.get(i, i) for i in universe)
                check('finite_supported_completion', len(set(image)) == n and image[:m] == vals)

    # Equality of edge labels is stronger than sibling orders and tree incidence.
    source = [(Q(0), Q(1)), (Q(1), Q(0))]
    target = [(Q(10), Q(30)), (Q(20), Q(40))]
    check('local_order_does_not_force_cross_level_label_coherence', profile(source[0], source[1]) == profile(target[0], target[1]) and source[0][1] == source[1][0] and target[0][1] != target[1][0])

    # The maximum fresh-choice branch can have constraints on both sides.
    a = [(Q(0), Q(-2)), (Q(0), Q(4))]
    b = [(Q(5), Q(-10)), (Q(5), Q(10))]
    r = extension_prefix(a, b, (Q(0), Q(1)))
    check('two_sided_fresh_cut', r[0] == 5 and -10 < r[1] < 10 and r[1] != 5)

    result = {
        'status': 'all assertions passed', 'seed': args.seed, 'trials': args.trials,
        'assertions': counts, 'total_assertions': sum(counts.values()),
        'scope': 'finite rational prefix-profile mechanisms and finite supported completions only',
        'not_verified': ['limit-prefix case', 'proper-class recursion', 'global homogeneity', 'exhaustiveness non-invariance', 'set-cardinal automorphism counts', 'Lean kernel correctness'],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
