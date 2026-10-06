"""Original exact counters for labeled cylindrical king placements.

No third-party implementation is imported or executed. The transfer encoding is
credited to Rintaro Matsuo in README.md; the row-mask counter works directly on
the physical board and does not use that encoding.
"""
from collections import defaultdict
from itertools import product


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    require(bool(a) and bool(b) and len(a[0]) == len(b), "Matrix shape mismatch")
    out = [[0] * len(b[0]) for _ in a]
    for i, row in enumerate(a):
        for k, value in enumerate(row):
            if value:
                for j, right in enumerate(b[k]):
                    if right:
                        out[i][j] += value * right
    return out


def power(a, exponent):
    require(exponent >= 0 and len(a) == len(a[0]), "Invalid matrix power")
    out = identity(len(a))
    while exponent:
        if exponent & 1:
            out = multiply(out, a)
        exponent //= 2
        if exponent:
            a = multiply(a, a)
    return out


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def transfer_matrix(word):
    """Entry u,v tests 0*1* forward and 1*0* backward, directly."""
    n = len(word)
    out = identity(n + 1)
    for u in range(n + 1):
        for v in range(n + 1):
            if u < v:
                out[u][v] = int(all(word[i] <= word[i + 1] for i in range(u, v - 1)))
            elif u > v:
                out[u][v] = int(all(word[i] >= word[i + 1] for i in range(v, u - 1)))
    return out


def component_matrix(word, color):
    labels = [0]
    for edge in word:
        labels.append(labels[-1] + int(edge != color))
    return [[int(label == j) for j in range(labels[-1] + 1)] for label in labels]


def intersection_tree(word):
    r = component_matrix(word, 0)
    s = component_matrix(word, 1)
    e0 = multiply(r, transpose(r))
    e1 = multiply(s, transpose(s))
    c = multiply(transpose(r), s)
    left, right = len(c), len(c[0])
    tree = [[0] * (left + right) for _ in range(left + right)]
    for i, row in enumerate(c):
        for j, value in enumerate(row):
            require(value in (0, 1), "Component intersections must be 0 or 1")
            tree[i][left + j] = tree[left + j][i] = value
    require(left + right == len(word) + 2, "Wrong tree vertex count")
    require(sum(map(sum, tree)) == 2 * (len(word) + 1), "Wrong tree edge count")
    seen, frontier = {0}, [0]
    while frontier:
        node = frontier.pop()
        for neighbor, edge in enumerate(tree[node]):
            if edge and neighbor not in seen:
                seen.add(neighbor)
                frontier.append(neighbor)
    require(len(seen) == len(tree), "Intersection graph is disconnected")
    return e0, e1, c, tree


def transfer_count(n, check_identities=True):
    if n == 0:
        return 1
    require(n >= 1, "n must be nonnegative")
    total = 0
    for word in product((0, 1), repeat=n):
        m = transfer_matrix(word)
        contribution = trace(power(m, n))
        if check_identities:
            e0, e1, c, tree = intersection_tree(word)
            require(m == multiply(e0, e1), f"M != E0 E1 for {word}")
            gram = multiply(c, transpose(c))
            require(contribution == trace(power(gram, n)), f"Gram trace failed for {word}")
            require(2 * contribution == trace(power(tree, 2 * n)), f"Tree trace failed for {word}")
        total += contribution
    return total


def board_count(n):
    """Independent row-mask DP on 2n rows, each a cycle of 2n squares.

    Horizontal shifts wrap. Vertical rows do not wrap. The state tracks the
    previous row and exact total king count; it never uses block thresholds.
    """
    require(n >= 0, "n must be nonnegative")
    if n == 0:
        return 1
    width, target = 2 * n, n * n
    full = (1 << width) - 1

    def left(mask):
        return ((mask << 1) & full) | (mask >> (width - 1))

    def right(mask):
        return (mask >> 1) | ((mask & 1) << (width - 1))

    masks = [mask for mask in range(1 << width) if not (mask & left(mask))]
    sizes = {mask: mask.bit_count() for mask in masks}
    compatible = {mask: [other for other in masks
                         if not (other & (mask | left(mask) | right(mask)))]
                  for mask in masks}
    dp = {mask: {sizes[mask]: 1} for mask in masks}
    for row in range(1, width):
        remaining = width - row - 1
        nxt = {mask: defaultdict(int) for mask in masks}
        for mask, counts in dp.items():
            for other in compatible[mask]:
                for count, ways in counts.items():
                    combined = count + sizes[other]
                    if combined <= target <= combined + remaining * n:
                        nxt[other][combined] += ways
        dp = nxt
    return sum(counts.get(target, 0) for counts in dp.values())
