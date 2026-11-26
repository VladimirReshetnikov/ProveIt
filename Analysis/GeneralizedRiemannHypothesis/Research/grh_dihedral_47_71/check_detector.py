"""Exact small-group checks of the Frobenius-weight minimum and excess identity."""
from collections import Counter
from itertools import permutations, product
from math import factorial


def cycle_type(permutation):
    unseen = set(range(len(permutation)))
    lengths = []
    while unseen:
        point = min(unseen)
        length = 0
        while point in unseen:
            unseen.remove(point)
            length += 1
            point = permutation[point]
        lengths.append(length)
    return tuple(sorted(lengths))


def nonlinear_characters(permutation):
    n = len(permutation)
    standard = sum(i == j for i, j in enumerate(permutation)) - 1
    if n == 3:
        return (standard,)
    # S4 acts on the three unordered ways to partition four points into pairs.
    fixed_pairings = 0
    for mate in (1, 2, 3):
        pair = {0, mate}
        image = {permutation[i] for i in pair}
        if image == pair or image.isdisjoint(pair):
            fixed_pairings += 1
    sign = (-1) ** (n - len(cycle_type(permutation)))
    return (standard, sign * standard, fixed_pairings - 1)


def verify(n, limit):
    elements = list(permutations(range(n)))
    order = factorial(n)
    size = Counter(cycle_type(g) for g in elements)
    classes = sorted(size)
    traces = {}
    for g in elements:
        kind = cycle_type(g)
        entry = nonlinear_characters(g)
        assert traces.setdefault(kind, entry) == entry
    identity = (1,) * n
    dims = traces[identity]
    even = {k for k in classes if (n - len(k)) % 2 == 0}
    optimum = {k: int(k in even and k != identity) for k in classes}
    accepted = attaining = 0
    for values in product(range(limit + 1), repeat=len(classes)):
        w = dict(zip(classes, values))
        excess = [
            -sum(size[k] * w[k] * traces[k][j] for k in classes) - d
            for j, d in enumerate(dims)
        ]  # |G| times the theorem's b_pi
        if any(v < 0 for v in excess):
            continue
        accepted += 1
        assert all(w[k] >= optimum[k] for k in classes)
        for k in even:
            gap = w[k] - w[identity] - optimum[k]
            assert order * gap == sum(
                b * (d - t) for b, d, t in zip(excess, dims, traces[k])
            )
        average_numerator = sum(
            size[k] * (w[k] - w[identity] - optimum[k]) for k in even
        )
        assert 2 * average_numerator == sum(b * d for b, d in zip(excess, dims))
        if sum(size[k] * w[k] for k in classes) == sum(
            size[k] * optimum[k] for k in classes
        ):
            assert w == optimum
            attaining += 1
    assert attaining == 1
    print(f"S{n}: {accepted} admissible integer weights in [0,{limit}]"
          f" on {len(classes)} classes; unique minimum {sorted(k for k in even if k != identity)}.")


if __name__ == "__main__":
    for degree in (3, 4):
        verify(degree, 5)
