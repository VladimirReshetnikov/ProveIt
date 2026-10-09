"""Deterministic workload constructors, with no external data dependency."""
from __future__ import annotations
import random
from rooted_disc.kernel import State, Candidate, partitions
from rooted_disc.assembly import Patch, Grammar


def canonical(blocks: list[list[int]], good: list[bool], charges: list[int], n: int):
    order = sorted(range(len(blocks)), key=lambda b: min(blocks[b]))
    p = [-1] * n
    for label, b in enumerate(order):
        for x in blocks[b]:
            p[x] = label
    if any(x < 0 for x in p):
        raise ValueError("incomplete partition")
    return tuple(p), tuple(good[b] for b in order), tuple(charges[b] if good[b] else 0 for b in order)


def operation(width: int, q: int, kind: str, i: int = 0, j: int = 1,
              charge: int = 0, bad: bool = False, cost: int = 0) -> Patch:
    blocks = [[x, width + x] for x in range(width)]
    flags, charges = [True] * width, [0] * width
    if kind == "identity":
        pass
    elif kind == "charge":
        charges[i] = charge
    elif kind == "bad":
        flags[i] = False
    elif kind == "join":
        a, b = sorted((i, j))
        blocks[a] += blocks[b]
        del blocks[b]; del flags[b]; del charges[b]
    elif kind == "reset":
        blocks[i] = [i]
        blocks.append([width + i]); flags.append(not bad); charges.append(charge if not bad else 0)
    elif kind == "swap":
        blocks[i][1], blocks[j][1] = blocks[j][1], blocks[i][1]
    else:
        raise ValueError("unknown operation")
    p, g, h = canonical(blocks, flags, charges, 2 * width)
    return Patch(width, width, p, g, h, cost, q)


def workload(width: int = 4, layers: int = 7, q: int = 4, seed: int = 271828,
             include_reset: bool = True) -> Grammar:
    rng = random.Random(seed)
    initial = State((0, 0) + tuple(range(1, width)), (True,) * width,
                    (1 if q > 1 else 0,) + (0,) * (width - 1), q)
    sequence = []
    for _ in range(layers):
        options = [operation(width, q, "identity", cost=rng.randrange(5))]
        for i in range(width):
            if q > 1:
                options.append(operation(width, q, "charge", i, charge=rng.randrange(1, q), cost=rng.randrange(5)))
            if i and include_reset:
                options.append(operation(width, q, "reset", i, bad=bool(rng.randrange(2)),
                                         charge=rng.randrange(q), cost=rng.randrange(5)))
            for j in range(i + 1, width):
                options.append(operation(width, q, "join", i, j, cost=rng.randrange(5)))
        sequence.append(tuple(options))
    # Separate disk caps keep any unrelated bad components in the final surface.
    sequence.append((Patch(width, 0, tuple(range(width)), (True,) * width, (0,) * width, 0, q),))
    return Grammar((Candidate(initial, 0),), tuple(sequence), None if q > 1 else 0,
                   "abstract-local-operations-v1")


def random_grammar(rng: random.Random, width: int = 2, layers: int = 3, options: int = 3, q: int = 4) -> Grammar:
    def random_state(n: int) -> State:
        p = rng.choice(list(partitions(n)))
        good = tuple(bool(rng.randrange(2)) for _ in range(max(p) + 1))
        h = tuple(rng.randrange(q) if g else 0 for g in good)
        return State(p, good, h, q)
    initial = tuple(Candidate(random_state(width + 1), rng.randrange(-4, 7)) for _ in range(2))
    sequence = []
    for _ in range(layers):
        layer = []
        for _ in range(options):
            s = random_state(2 * width)
            layer.append(Patch(width, width, s.partition, s.good, s.charges, rng.randrange(-4, 7), q))
        sequence.append(tuple(layer))
    cap = []
    for _ in range(2):
        s = random_state(width)
        cap.append(Patch(width, 0, s.partition, s.good, s.charges, rng.randrange(-4, 7), q))
    sequence.append(tuple(cap))
    return Grammar(initial, tuple(sequence), None if q > 1 else 0)
