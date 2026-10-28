"""Exact minimax selection of a balanced streamed separator tree.

The groups are fixed in the theorem (r=16).  The selector uses 14,827
subset states and 462,465 unordered splits, rather than enumerating 16!
labelings.  It optimizes index-length cost, not measured SAT runtime.
"""
from functools import lru_cache
from itertools import combinations


def ceil_log2(n):
    if not isinstance(n, int) or n < 1:
        raise ValueError("index list size must be a positive integer")
    return (n - 1).bit_length()


def pair_weights(dimensions, groups):
    return {(a, b): ceil_log2(dimensions.get((a, b), 1)) +
                     ceil_log2(dimensions.get((b, a), 1))
            for a in range(groups) for b in range(a + 1, groups)}


def optimal_balanced_tree(weights, groups=16):
    if groups < 1 or groups & (groups - 1):
        raise ValueError("the group count must be a power of two")
    normalized = {(a, b): int(weights.get((a, b), 0))
                  for a in range(groups) for b in range(a + 1, groups)}
    if any(w < 0 for w in normalized.values()):
        raise ValueError("negative index-length weight")
    internal = [0] * (1 << groups)
    for mask in range(1, 1 << groups):
        bit = mask & -mask
        vertex = bit.bit_length() - 1
        rest = mask ^ bit
        extra = 0
        pending = rest
        while pending:
            other_bit = pending & -pending
            other = other_bit.bit_length() - 1
            extra += normalized[min(vertex, other), max(vertex, other)]
            pending ^= other_bit
        internal[mask] = internal[rest] + extra

    choices = {}
    stats = {"states": 0, "unordered_splits": 0,
             "internal_weight_masks": 1 << groups}

    @lru_cache(None)
    def solve(mask):
        stats["states"] += 1
        if mask & (mask - 1) == 0:
            return 0
        low = mask & -mask
        vertices = tuple(v for v in range(groups) if (mask ^ low) >> v & 1)
        half = mask.bit_count() // 2
        best = None
        for selected in combinations(vertices, half - 1):
            left = low | sum(1 << v for v in selected)
            right = mask ^ left
            cut = internal[mask] - internal[left] - internal[right]
            score = cut + max(solve(left), solve(right))
            stats["unordered_splits"] += 1
            if best is None or score < best:
                best = score
                choices[mask] = left
        return best

    full = (1 << groups) - 1
    cost = solve(full)

    def reconstruct(mask):
        if mask & (mask - 1) == 0:
            return mask.bit_length() - 1
        left = choices[mask]
        return reconstruct(left), reconstruct(mask ^ left)

    return reconstruct(full), cost, stats


def leaf_paths(tree, weights, inherited=0):
    """Independent direct interpretation of a tree's separator costs."""
    if isinstance(tree, int):
        return [(tree, inherited)]
    def leaves(branch):
        if isinstance(branch, int):
            return [branch]
        return leaves(branch[0]) + leaves(branch[1])
    left, right = tree
    cross = sum(weights.get(tuple(sorted((a, b))), 0)
                for a in leaves(left) for b in leaves(right))
    return (leaf_paths(left, weights, inherited + cross) +
            leaf_paths(right, weights, inherited + cross))


def all_balanced_trees(vertices):
    """Independent exhaustive oracle, used only for small test group counts."""
    if len(vertices) == 1:
        yield vertices[0]
        return
    first, rest = vertices[0], vertices[1:]
    for selected in combinations(rest, len(vertices) // 2 - 1):
        left = (first,) + selected
        right = tuple(v for v in rest if v not in selected)
        for a in all_balanced_trees(left):
            for b in all_balanced_trees(right):
                yield a, b
