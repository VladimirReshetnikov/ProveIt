"""Construct the fan colouring from the chapter and check its edge certificates.

Run python3 vizing.py for all labelled simple graphs of order at most six,
then fixed-seed graphs with shuffled edges to exercise both Kempe branches.
Only the Python standard library is required.
"""

from collections import Counter
from itertools import combinations
from random import Random


def edge(u, v):
    return (u, v) if u < v else (v, u)


def is_proper(n, edges, colouring, palette_size):
    if {edge(u, v) for u, v in edges} != set(colouring):
        return False
    used = [set() for _ in range(n)]
    for (u, v), c in colouring.items():
        if not (0 <= u < v < n and 0 <= c < palette_size):
            return False
        if c in used[u] or c in used[v]:
            return False
        used[u].add(c)
        used[v].add(c)
    return True


def vizing(n, edges, branches=None):
    """Colour a loopless simple graph in the supplied edge order.

    Returns a dictionary on sorted endpoint pairs, with colours starting at 0.
    """
    edges = list(edges)
    degree = [0] * n
    seen = set()
    for x, y in edges:
        if not (0 <= x < n and 0 <= y < n and x != y) or edge(x, y) in seen:
            raise ValueError("expected distinct, loopless edges with valid endpoints")
        seen.add(edge(x, y))
        degree[x] += 1
        degree[y] += 1
    palette = set(range(max(degree, default=0) + 1))
    colouring = {}

    def missing(v):
        return palette.difference(c for e, c in colouring.items() if v in e)

    for t, (x, y) in enumerate(edges):
        fan = [y]
        parent = [-1]
        while True:
            for j, w in enumerate(fan):
                allowed = missing(w)
                candidates = [v for v in range(n) if v not in fan and
                              colouring.get(edge(x, v)) in allowed]
                if candidates:
                    fan.append(candidates[0])
                    parent.append(j)
                    break
            else:
                break

        target = len(fan) - 1
        alpha = min(missing(x))
        beta = min(missing(fan[target]))
        fill = beta
        branch = "common missing colour"
        if beta not in missing(x):
            j = next(j for j in range(1, len(fan))
                     if colouring[edge(x, fan[j])] == beta)
            i = parent[j]
            two_colour = [[] for _ in range(n)]
            for (u, v), col in colouring.items():
                if col in (alpha, beta):
                    two_colour[u].append(v)
                    two_colour[v].append(u)

            def component(start):
                found, stack = {start}, [start]
                while stack:
                    for v in two_colour[stack.pop()]:
                        if v not in found:
                            found.add(v)
                            stack.append(v)
                return found

            if fan[i] not in component(x):
                target = i
                branch = "swap at predecessor"
            else:
                branch = "swap at final fan vertex"
            swap = component(fan[target])
            assert x not in swap
            for e, col in list(colouring.items()):
                if e[0] in swap and col in (alpha, beta):
                    colouring[e] = beta if col == alpha else alpha
            fill = alpha

        chain = [target]
        while chain[-1] != 0:
            chain.append(parent[chain[-1]])
        chain.reverse()
        for before, after in zip(chain, chain[1:]):
            colouring[edge(x, fan[before])] = colouring[edge(x, fan[after])]
        colouring[edge(x, fan[target])] = fill
        assert is_proper(n, edges[:t+1], colouring, len(palette))
        if branches is not None:
            branches[branch] += 1
    return colouring


def main():
    branches = Counter()
    total = 0
    for n in range(7):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [e for i, e in enumerate(pairs) if mask >> i & 1]
            vizing(n, edges, branches)
            total += 1
    print(f"All {total} labelled graphs through order 6 passed.")
    rand = Random(27591)
    for _ in range(150):
        n = rand.randrange(7, 15)
        edges = [e for e in combinations(range(n), 2) if rand.randrange(4)]
        rand.shuffle(edges)
        vizing(n, edges, branches)
    assert len(branches) == 3
    print("150 further deterministic shuffled-edge cases passed.")
    print("Extension branches:", dict(branches))


if __name__ == "__main__":
    main()
