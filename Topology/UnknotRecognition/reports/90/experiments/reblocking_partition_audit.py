"""Independent exhaustive audit of through-component reblocking.

Standard-library only.  Enumerates every block bijection up to width five by
default, expands successive finite graph powers, and tests component partitions.
It imports no production routing or signature code.  Run, for example:
    python reblocking_partition_audit.py --max-width 5 --output audit.json
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import itertools
import json
from pathlib import Path


@dataclass(frozen=True)
class Tile:
    n: int
    edges: tuple[tuple[int, int], ...]
    left: tuple[int, ...]
    right: tuple[int, ...]


def partitions(n):
    """Restricted-growth words enumerate each unordered set partition once."""
    def extend(word, maximum):
        if len(word) == n:
            yield tuple(tuple(i for i, value in enumerate(word) if value == a)
                        for a in range(maximum + 1))
            return
        for a in range(maximum + 2):
            yield from extend(word + [a], max(maximum, a))
    yield from extend([0], 0)


def source_tile(left, right, permutation):
    width = sum(map(len, left))
    edges = []
    for i, part in enumerate(left):
        vertices = list(part) + [width + a for a in right[permutation[i]]]
        edges.extend((vertices[j - 1], vertices[j])
                     for j in range(1, len(vertices)))
    return Tile(2 * width, tuple(edges), tuple(range(width)),
                tuple(range(width, 2 * width)))


def append(left, right):
    """Explicit graph composition; there is no connectivity-state recurrence."""
    n = left.n
    image = {v: left.right[i] for i, v in enumerate(right.left)}
    for v in range(right.n):
        if v not in image:
            image[v] = n
            n += 1
    edges = left.edges + tuple((image[a], image[b]) for a, b in right.edges)
    return Tile(n, edges, left.left, tuple(image[v] for v in right.right))


def component_partitions(tile):
    parent = list(range(tile.n))

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for a, b in tile.edges:
        parent[root(a)] = root(b)
    components = {root(v) for v in range(tile.n)}
    input_parts = []
    output_parts = []
    for component in components:
        a = tuple(i for i, v in enumerate(tile.left) if root(v) == component)
        b = tuple(i for i, v in enumerate(tile.right) if root(v) == component)
        if not a or not b:
            raise AssertionError("a finite source power lost the through property")
        input_parts.append(a)
        output_parts.append(b)
    return len(components), set(input_parts) == set(output_parts)


def audit(max_width):
    widths = []
    total = 0
    strict_drops = 0
    for width in range(1, max_width + 1):
        choices = list(partitions(width))
        count = 0
        largest_m = 0
        sharp_example = None
        for left in choices:
            for right in choices:
                if len(left) != len(right):
                    continue
                for permutation in itertools.permutations(range(len(left))):
                    tile = source_tile(left, right, permutation)
                    power = tile
                    d = len(left)
                    for exponent in range(1, d + 1):
                        rank, aligned = component_partitions(power)
                        if aligned:
                            if exponent > d - rank + 1:
                                raise AssertionError("refined stabilization bound failed")
                            if exponent > largest_m:
                                largest_m = exponent
                                sharp_example = {
                                    "left_partition": left,
                                    "right_partition": right,
                                    "block_bijection": permutation,
                                    "initial_components": d,
                                    "stable_components": rank,
                                }
                            break
                        following = append(power, tile)
                        next_rank, _ = component_partitions(following)
                        if next_rank >= rank:
                            raise AssertionError("unaligned power did not strictly drop rank")
                        strict_drops += 1
                        power = following
                    else:
                        raise AssertionError("no aligned power by original component count")
                    count += 1
        total += count
        widths.append({"width": width, "diagrams": count,
                       "maximum_first_aligned_exponent": largest_m,
                       "example_attaining_maximum": sharp_example})
    return {"all_passed": True, "maximum_width": max_width,
            "total_diagrams": total, "strict_rank_drops_checked": strict_drops,
            "method": "exhaustive block bijections; explicit finite graph composition",
            "widths": widths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_width <= 6:
        parser.error("the intentionally finite audit supports widths 1 through 6")
    result = audit(args.max_width)
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
