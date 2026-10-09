"""Deterministic explicit fixtures. Bell-sized inputs are used only in benchmarks.

Construction time is separately declared; a large initial list is not generated
for free by any complexity theorem.
"""
import random
from envelope_kernel import Candidate, canonical, partitions
from grammar import Grammar, Patch


def identity_patch(r):
    return tuple(range(r)) + tuple(range(r))


def merge_patch(r, a, b):
    x = list(range(r))
    x[b] = x[a]
    return canonical(x + x)


def restricted_grammar(r=7, lam=2, depth=8, seed=20261009):
    if not 0 <= lam < r:
        raise ValueError('require 0 <= lambda < r')
    rng = random.Random(seed + r * 71 + lam)
    ps = list(partitions(r))
    rho = (0,) * (lam + 1) + tuple(range(1, r - lam))
    initial = tuple(Candidate(p, rng.randrange(-1000, 1001)) for p in ps)
    patches = [Patch(identity_patch(r), 0)]
    patches += [Patch(merge_patch(r, a, b), (a + 2*b) % 7 - 3)
                for a in range(lam + 1) for b in range(a + 1, lam + 1)]
    return Grammar((r,) * (depth + 1), initial, (tuple(patches),) * depth,
                   (Candidate(rho),))


def random_grammar(rng, max_width=5, depth=3):
    widths = tuple(rng.randrange(1, max_width + 1) for _ in range(depth + 1))
    def rp(n):
        return canonical(rng.randrange(n) for _ in range(n))
    initial = tuple(Candidate(rp(widths[0]), rng.randrange(-20, 21), rng.randrange(4))
                    for _ in range(rng.randrange(1, 10)))
    layers = tuple(tuple(Patch(rp(a + b), rng.randrange(-10, 11), rng.randrange(4))
                         for _ in range(rng.randrange(1, 5)))
                   for a, b in zip(widths, widths[1:]))
    caps = tuple(Candidate(rp(widths[-1]), rng.randrange(-10, 11), rng.randrange(4))
                 for _ in range(rng.randrange(1, 6)))
    return Grammar(widths, initial, layers, caps,
                   tuple(sorted(rng.sample(range(4), rng.randrange(1, 5)))))


def wide_envelope(r=128, lam=3):
    if not 0 <= lam < r:
        raise ValueError('bad rank')
    # One past vertex, lambda+1 parallel edges to one future vertex;
    # the remaining future vertices are pendant leaves.
    return (0,) * r, (0,) * (lam + 1) + tuple(range(1, r - lam))
