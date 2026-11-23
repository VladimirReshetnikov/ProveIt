#!/usr/bin/env python3
"""Check finite walk counts and compare spin sums with graphical expansions."""
from itertools import product
from math import prod


def check_walks():
    moves = ((1, 0), (-1, 0), (0, 1), (0, -1))
    histogram = [0] * 9
    restricted = [0] * 9
    seen = {(0, 0)}

    def walk(x, y, length, nonwest):
        histogram[length] += 1
        restricted[length] += int(nonwest)
        if length == len(histogram) - 1:
            return
        for dx, dy in moves:
            nxt = (x + dx, y + dy)
            if nxt not in seen:
                seen.add(nxt)
                walk(*nxt, length + 1, nonwest and dx != -1)
                seen.remove(nxt)

    walk(0, 0, 0, True)
    assert histogram == [1, 4, 12, 36, 100, 284, 780, 2172, 5916]
    assert restricted[:2] == [1, 3]
    assert all(c == 2 * b + a for a, b, c in zip(restricted, restricted[1:], restricted[2:]))


def lattice(w, h):
    """Construct primal edges and crossed dual edges in the same order."""
    outside = w * h

    def vertex(x, y):
        return y * (w + 1) + x

    def face(x, y):
        return y * w + x if 0 <= x < w and 0 <= y < h else outside

    primal, dual = [], []
    for y in range(h + 1):
        for x in range(w):
            primal.append((vertex(x, y), vertex(x + 1, y)))
            dual.append((face(x, y - 1), face(x, y)))
    for x in range(w + 1):
        for y in range(h):
            primal.append((vertex(x, y), vertex(x, y + 1)))
            dual.append((face(x - 1, y), face(x, y)))
    return primal, dual


def spin_sum(n, edges, weights, marked=0, fixed_last=False):
    value = 0
    for spin in range(1 << (n - int(fixed_last))):
        sign = -1 if (marked & spin).bit_count() % 2 else 1
        factors = (ab[((spin >> u) ^ (spin >> v)) & 1]
                   for (u, v), ab in zip(edges, weights))
        value += sign * prod(factors)
    return value


def check_grid(w, h):
    primal, dual = lattice(w, h)
    n, cells, bonds = (w + 1) * (h + 1), w * h, len(primal)
    weights = [(2 + i % 3, 1 + i % 2) for i in range(bonds)]
    expanded = [(a + b, a - b) for a, b in weights]
    by_boundary = {}
    even_count = 0
    for mask in range(1 << bonds):
        boundary = 0
        factor = 1
        for i, (u, v) in enumerate(primal):
            selected = mask >> i & 1
            factor *= expanded[i][selected]
            if selected:
                boundary ^= (1 << u) ^ (1 << v)
        by_boundary[boundary] = by_boundary.get(boundary, 0) + factor
        even_count += int(boundary == 0)
    assert even_count == 1 << cells
    for marked in (0, 1, 3, (1 << (n - 1)) + 1):
        direct = spin_sum(n, primal, weights, marked)
        assert (direct << bonds) == (by_boundary.get(marked, 0) << n)
    dual_plus = spin_sum(cells + 1, dual, expanded, fixed_last=True)
    dual_free = spin_sum(cells + 1, dual, expanded)
    assert dual_free == 2 * dual_plus == 2 * by_boundary[0]


def check_rings():
    for n, (a, b) in product(range(3, 8), ((3, 1), (1, 2), (2, 2))):
        edges = [(i, (i + 1) % n) for i in range(n)]
        weights = [(a, b)] * n
        p, q = a + b, a - b
        assert spin_sum(n, edges, weights) == p ** n + q ** n
        for d in range(1, n):
            assert spin_sum(n, edges, weights, 1 | (1 << d)) == q ** d * p ** (n-d) + p ** d * q ** (n-d)


if __name__ == '__main__':
    check_walks()
    for dimensions in ((1, 1), (1, 2), (2, 1), (2, 2)):
        check_grid(*dimensions)
    check_rings()
    print("Walk counts, restricted recurrence, finite Ising duality, defects and ring checks passed.")
