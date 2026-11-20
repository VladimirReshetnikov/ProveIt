"""Boundary ranks for the 13-vertex threefold attachment in the report."""
from itertools import combinations


def rank_mod(columns, prime):
    pivots = {}
    for column in columns:
        col = [v % prime for v in column]
        for i in range(len(col)):
            if not col[i]:
                continue
            if i not in pivots:
                inverse = pow(col[i], -1, prime)
                pivots[i] = [(v * inverse) % prime for v in col]
                break
            c = col[i]
            col = [(v - c * w) % prime for v, w in zip(col, pivots[i])]
    return len(pivots)


def boundary_columns(upper, lower):
    where = {s: i for i, s in enumerate(lower)}
    for simplex in upper:
        col = [0] * len(lower)
        for i in range(len(simplex)):
            face = simplex[:i] + simplex[i + 1:]
            col[where[face]] = (-1) ** i
        yield col


def main():
    triangles = []
    for i in range(9):
        a, b = i, (i + 1) % 9
        c, d = 9 + i % 3, 9 + (i + 1) % 3
        for tri in ((a, b, d), (a, c, d), (12, a, b)):
            triangles.append(tuple(sorted(tri)))
    edges = sorted({e for t in triangles for e in combinations(t, 2)})
    vertices = [(i,) for i in range(13)]
    assert (len(vertices), len(edges), len(triangles)) == (13, 39, 27)
    for prime, expected in ((2, (1, 0, 0)), (3, (1, 1, 1))):
        r1 = rank_mod(boundary_columns(edges, vertices), prime)
        r2 = rank_mod(boundary_columns(triangles, edges), prime)
        betti = (len(vertices)-r1, len(edges)-r1-r2, len(triangles)-r2)
        assert betti == expected
        print(f"Threefold attachment over F_{prime}: boundary ranks {r1}, {r2}; Betti {betti}.")


if __name__ == "__main__":
    main()
