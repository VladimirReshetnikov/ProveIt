"""Exact finite verification of the root-lattice diameter bounds; Python 3.10+."""
from argparse import ArgumentParser
from itertools import combinations, product
from math import comb


def balanced_size(rank, diameter):
    p = (diameter + 1) // 2
    q = diameter // 2
    return sum(comb(rank, j) * comb(p, j) * comb(q + rank - j, rank - j)
               for j in range(min(rank, p) + 1))


def normalized_layer(rank, diameter, total):
    return [prefix + (total - sum(prefix),)
            for prefix in product(range(diameter + 1), repeat=rank)
            if 0 <= total - sum(prefix) <= diameter]


def subsets_to_check(rank):
    coords = range(rank + 1)
    cuts = []
    for size in range(2, (rank + 1) // 2 + 1):
        for cut in combinations(coords, size):
            if 2 * size != rank + 1 or 0 in cut:
                cuts.append(cut)
    return sorted(cuts, key=len, reverse=True)


def interval_masks(points, cut, diameter):
    values = [sum(pt[j] for j in cut) for pt in points]
    smallest, largest = min(values), max(values)
    # If largest-smallest < diameter, the single full interval is enough.
    starts = range(smallest, max(smallest, largest - diameter) + 1)
    masks = []
    for lo in starts:
        m = sum(1 << i for i, v in enumerate(values) if lo <= v <= lo + diameter)
        masks.append(m)
    return masks


def verify(rank, diameter):
    target = balanced_size(rank, diameter)
    total_nodes = 0
    m = rank + 1
    p = (diameter + 1) // 2
    q = diameter // 2
    shapes = []
    for a, b in [(p, q), (q, p)]:
        shape = {pt for pt in normalized_layer(rank, diameter, m * b + a - b)
                 if sum(max(v - b, 0) for v in pt) <= a}
        shapes.append(shape)
    for total in range((rank + 1) * diameter // 2 + 1):
        points = normalized_layer(rank, diameter, total)
        if len(points) < target:
            continue
        all_masks = [interval_masks(points, cut, diameter)
                     for cut in subsets_to_check(rank)]
        # Large cuts are applied first; every cut is imposed on unpruned branches.
        def visit(candidates, level):
            nonlocal total_nodes
            total_nodes += 1
            if candidates.bit_count() < target:
                return
            if level == len(all_masks):
                survivors = [pt for i, pt in enumerate(points) if (candidates >> i) & 1]
                minima = list(map(min, zip(*survivors)))
                normalized = {tuple(v - a for v, a in zip(pt, minima)) for pt in survivors}
                if len(normalized) != target or normalized not in shapes:
                    raise AssertionError((rank, diameter, total, len(normalized)))
                return
            for mask in all_masks[level]:
                visit(candidates & mask, level + 1)
        visit((1 << len(points)) - 1, 0)
    return target, total_nodes


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('rank', type=int)
    parser.add_argument('diameters', type=int, nargs='+')
    args = parser.parse_args()
    for d in args.diameters:
        target, nodes = verify(args.rank, d)
        print(f'rank={args.rank} diameter={d} maximum={target} equality=translate_or_negative nodes={nodes}', flush=True)
