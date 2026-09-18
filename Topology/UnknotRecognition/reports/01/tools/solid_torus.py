"""A nine-tetrahedron S^1 x triangle, and a primitive non-exact integer cocycle."""
from itertools import combinations


def example():
    tets = []
    for layer in range(3):
        a, b, c = [3 * layer + j for j in range(3)]
        d, e, f = [3 * ((layer + 1) % 3) + j for j in range(3)]
        tets.extend([(a, b, c, f), (a, b, e, f), (a, d, e, f)])
    edges = {tuple(sorted(edge)) for t in tets for edge in combinations(t, 2)}
    cocycle = {(u, v): -1 for u, v in edges if u // 3 == 0 and v // 3 == 2}
    return tets, cocycle
