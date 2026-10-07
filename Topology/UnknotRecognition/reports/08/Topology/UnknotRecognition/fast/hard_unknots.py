"""Unknot diagrams for timing the whole pipeline.

``make`` gives scrambled unknot braids: the closure of v u v^-1 with
u = s_1 ... s_{n-1}, rewritten by random braid relations, far commutations and
inserted cancelling pairs.  About half of them survive Reidemeister I/II with 15
to 27 crossings and pass the Alexander and Jones filters.  They are a WEAK family:
the rewriting consists of Reidemeister III moves, and the III-assisted reduction
of ``simplify`` undoes all of them (120 of 120, and 180 of 180 with heavier
scrambling), already at depth 1.  They remain useful with ``simplify(d, r3=False)``.

``SURVIVORS`` are the honest hard inputs: closures found by random search that
survive Reidemeister I and II, the budgeted depth-4 III search of ``simplify`` and
the Alexander filter, and are unknots by reduced Khovanov rank 1.  They are rare:
15 among 60000 random words of 16 to 33 letters (seed 2029), plus 7 of the 117
that survived a depth-1 search among 40000 words (seed 2028); the largest has 16
crossings.  Each entry is (crossings after reduction, strands, braid word).

Usage:  python hard_unknots.py            reports how the pipeline decides both families
"""
from __future__ import annotations

import random


SURVIVORS = [
    (16, 5, [1, 1, -1, -2, 4, -2, 2, -3, 2, -4, 3, 4, -3, 3, -4, -3, -4, -4, -3, 3, 3, 3, 2, 4, 1, 1, -3, 3, -2, -3]),
    (15, 5, [-4, -4, 2, 4, 2, -3, -2, -4, -4, -3, 4, 2, -2, -1, -1, -4, 2, -2, -4, -2, 4, 4, 3, 3, -2, -1, 2, 4]),
    (15, 6, [3, -4, -1, -3, 1, -2, -5, -2, -2, -1, -1, -2, 4, 3, -4, -2, 4, 4, 1, 5, 5, 4, 3]),
    (13, 4, [-1, -1, -1, -1, -2, 1, -2, 1, 3, 3, 2, -2, -1, 1, -1, 1, -1, -2, -3, 3, 3, 3, -3, 2, 2]),
    (13, 5, [-1, 3, -1, -4, 4, 1, -3, 2, 4, 1, -1, 3, -2, 2, -2, 1, -2, -2, 2, 4, -1, -2, -1, -1, 2, -1, 2, 1, 4, -3]),
    (13, 6, [5, -4, -1, 2, 4, -1, -1, 2, -3, 4, -2, 5, -5, -5, 4, -1, 4, 5, -3, 1, 4, 5, 3, -3, -4]),
    (12, 4, [-1, 3, 3, -2, 2, -3, -2, -1, -3, -1, -1, -2, -1, 3, 2, -3, 2, 2, 1, 1, 3]),
    (12, 4, [2, -3, 2, 3, 2, 3, 3, -2, -3, -3, 2, -1, -2, -1, -2, 3, -2, 3, 1]),
    (11, 4, [-3, -3, -3, 2, -3, 2, -2, 1, 1, -2, 2, -1, -1, 2, 1, 1, -3, 3, -2, 1, -2]),
    (11, 4, [3, -2, 1, -1, -2, -3, -1, 3, 1, 2, 3, -2, -1, 2, 1, -1, -1, -1, -1, -1, 1, 2, 1, -2, -1, -2, 1, 2, 3]),
    (11, 5, [-1, -3, 3, 2, 4, -4, -3, -1, -2, 2, 2, 1, 3, 4, -1, 3, -2, 4, 4, -1]),
    (11, 5, [2, -2, -2, 1, 1, -3, 2, 4, -1, 2, -3, -1, -1, -2, 4, 4, -3, 3, -2, -1, -2, 2]),
]


def scramble(word: list[int], rng: random.Random, steps: int) -> list[int]:
    w = list(word)
    for _ in range(steps):
        i = rng.randrange(len(w) - 1)
        a, b = w[i], w[i + 1]
        if abs(abs(a) - abs(b)) >= 2:                                    # far commutation
            w[i], w[i + 1] = b, a
        elif i + 2 < len(w) and abs(abs(a) - abs(b)) == 1 and w[i + 2] == a and (a > 0) == (b > 0):
            w[i], w[i + 1], w[i + 2] = b, a, b                           # s_i s_j s_i = s_j s_i s_j
        elif rng.random() < 0.15:                                        # a cancelling pair
            g = rng.choice((1, -1)) * rng.randrange(1, max(abs(x) for x in w) + 1)
            w[i + 1:i + 1] = [g, -g]
    return w


def make(strands: int, conjugator_length: int = 10, steps: int = 400, seed: int = 0) -> list[int]:
    """A braid word on ``strands`` strands whose closure is an unknot."""
    rng = random.Random(seed)
    v = [rng.choice((1, -1)) * rng.randrange(1, strands) for _ in range(conjugator_length)]
    return scramble(v + list(range(1, strands)) + [-g for g in reversed(v)], rng, steps)


if __name__ == "__main__":
    from collections import Counter

    from fastunknot import Diagram, recognize

    methods = Counter(recognize(Diagram.from_braid(strands, make(strands, seed=seed))).method
                      for strands in (4, 5, 6) for seed in range(40))
    print("scrambled family, 120 diagrams:", dict(methods))
    for crossings, strands, word in SURVIVORS:
        result = recognize(Diagram.from_braid(strands, word))
        print(f"survivor: {result.reduced_crossings:2d} crossings after reduction, {result.status}, "
              f"{result.method}, {result.seconds * 1000:.2f} ms")
