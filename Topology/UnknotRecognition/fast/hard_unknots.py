"""Scrambled unknot diagrams that no filter decides: inputs for timing the whole pipeline.

The closure of v u v^-1 with u = s_1 s_2 ... s_{n-1} is an unknot.  Written like
that it collapses under Reidemeister II moves, so the word is first rewritten by
random braid relations, far commutations and inserted cancelling pairs.  About
half of the results survive the R1/R2 reduction with 15 to 27 crossings and pass
the Alexander and Jones filters (they are unknots), so the Khovanov scan decides.

Usage:  python hard_unknots.py            lists the survivors for the default parameters
"""
from __future__ import annotations

import random


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
    from fastunknot import Diagram, recognize

    for strands in (4, 5, 6):
        for seed in range(40):
            result = recognize(Diagram.from_braid(strands, make(strands, seed=seed)))
            if result.method == "reduced-khovanov-F2-scan":
                print(f"strands {strands} seed {seed:2d}: {result.reduced_crossings:2d} crossings after reduction, "
                      f"{result.status}, {result.seconds * 1000:.2f} ms")
