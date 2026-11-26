#!/usr/bin/env python3
"""Exact prefix certificates for uniform four-prime Rankin optimality."""
from fractions import Fraction
from itertools import product
from math import prod

LENGTHS = (9, 9, 3, 3)
DEPTHS = (2, 2, 1, 1)
MULTIPLIER = Fraction(21, 20)


def ternary_good(e):
    while e:
        e, digit = divmod(e, 3)
        if digit == 2:
            return False
    return True


def prefix_certificate(primes, lengths):
    """Bound 20 times good weight plus 21 times other weight on the prefix."""
    box = product(*(range(n) for n in lengths))
    points = sorted((prod(p**i for p, i in zip(primes, e)), all(map(ternary_good, e))) for e in box)
    vals = [v for v, _ in points]
    ceiling = vals[-1]
    weights = [(20 if ok else 21) * (ceiling // v) for v, ok in points]
    target = sum(w for w, (_, ok) in zip(weights, points) if ok)
    ix = {v: i for i, v in enumerate(vals)}
    # Each earlier endpoint and midpoint force the third value's exclusion.
    triples = [[] for _ in vals]
    for i, midpoint in enumerate(vals):
        for j in range(i):
            third, rem = divmod(midpoint**2, vals[j])
            if not rem and third in ix:
                triples[i].append((1 << j, 1 << ix[third]))
    nodes = 0
    def bound(chosen, undecided, upper):
        nonlocal nodes
        nodes += 1
        if upper <= target:
            return
        if not undecided:
            raise ValueError(f"threshold exceeded for {primes}, {lengths}")
        vertex = undecided & -undecided
        i = vertex.bit_length() - 1
        after = undecided ^ vertex
        bound(chosen, after, upper - weights[i])
        kills = 0
        for first_bit, third_bit in triples[i]:
            if chosen & first_bit:
                kills |= third_bit
        kills &= after
        after ^= kills
        while kills:
            bit = kills & -kills
            upper -= weights[bit.bit_length() - 1]
            kills ^= bit
        bound(chosen | vertex, after, upper)
    bound(0, (1 << len(points)) - 1, sum(weights))
    return nodes


def tail_charge(primes):
    answer = Fraction(0)
    for step in (1, 2):
        low = prod(1 + Fraction(1, p**(step * 3**j))
                   for p, k in zip(primes, DEPTHS) for j in range(k))
        high = prod(1 / (1 - Fraction(1, p**(step*n))) for p,n in zip(primes,LENGTHS))
        answer += low * (high - 1)
    return answer


if __name__ == "__main__":
    for primes, frozen in [((2,3,5,7),2), ((2,5,7,11),1), ((3,5,7,11),1)]:
        boxes = 0
        nodes = 0
        prefix_lengths = [(n,) if i < frozen else range(1,n+1) for i,n in enumerate(LENGTHS)]
        for sizes in product(*prefix_lengths):
            nodes += prefix_certificate(primes, sizes)
            boxes += 1
        margin = 1 - 1 / MULTIPLIER - tail_charge(primes)
        assert margin > Fraction(1,200)
        print(f"{primes}, fixed coordinates {frozen}: {boxes} prefixes, {nodes} search nodes, margin > 1/200",flush=True)
    assert prod(Fraction(p,p-1) for p in (5,7,11,13)) < 2
