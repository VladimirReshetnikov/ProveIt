"""Independent small-diagram reduced Khovanov cube over F2.

This is a validation/reference fallback, NOT a fast Khovanov implementation.
It expands all resolutions and basis vectors. Passing both limits as None
selects an uncapped exponential decision backend for knot closures.
"""
from __future__ import annotations
from collections.abc import Iterable
from .common import validate_word


class CubeLimit(RuntimeError):
    pass


def _components(strands: int, word: tuple[int, ...], mask: int) -> tuple[list[int], int]:
    count = (len(word) + 1) * strands
    parent = list(range(count))

    def root(a: int) -> int:
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    def join(a: int, b: int) -> None:
        a, b = root(a), root(b)
        if a != b:
            parent[b] = a

    for level, generator in enumerate(word):
        crossing = abs(generator) - 1
        bit = (mask >> level) & 1
        turnback = bool(bit) if generator > 0 else not bool(bit)
        top, bottom = level * strands, (level + 1) * strands
        for j in range(strands):
            if not turnback or j not in (crossing, crossing + 1):
                join(top + j, bottom + j)
        if turnback:
            join(top + crossing, top + crossing + 1)
            join(bottom + crossing, bottom + crossing + 1)
    for j in range(strands):
        join(j, len(word) * strands + j)
    indices: dict[int, int] = {}
    labels: list[int] = []
    for j in range(count):
        r = root(j)
        if r not in indices:
            indices[r] = len(indices)
        labels.append(indices[r])
    return labels, len(indices)


def _insert_marked_bit(x: int, mark: int) -> int:
    low = x & ((1 << mark) - 1)
    return low | (1 << mark) | ((x >> mark) << (mark + 1))


def _remove_marked_bit(x: int, mark: int) -> int:
    if not ((x >> mark) & 1):
        raise AssertionError('differential left the reduced subcomplex')
    return (x & ((1 << mark) - 1)) | ((x >> (mark + 1)) << mark)


def _saddle_images(source_bits: int, relation: list[set[int]], target_circles: int
                   ) -> tuple[int, ...]:
    source_circles = len(relation)
    if target_circles == source_circles - 1:
        incoming: list[list[int]] = [[] for _ in range(target_circles)]
        for i, targets in enumerate(relation):
            if len(targets) != 1:
                raise AssertionError('invalid merge relation')
            incoming[next(iter(targets))].append(i)
        output = 0
        for j, sources in enumerate(incoming):
            dots = sum((source_bits >> i) & 1 for i in sources)
            if dots >= 2:
                return ()
            if dots:
                output |= 1 << j
        return (output,)
    if target_circles == source_circles + 1:
        output = 0
        split: tuple[int, ...] | None = None
        undotted = False
        for i, targets in enumerate(relation):
            dot = (source_bits >> i) & 1
            if len(targets) == 1:
                if dot:
                    output |= 1 << next(iter(targets))
            elif len(targets) == 2 and split is None:
                split = tuple(sorted(targets))
                if dot:
                    output |= (1 << split[0]) | (1 << split[1])
                else:
                    undotted = True
            else:
                raise AssertionError('invalid split relation')
        if split is None:
            raise AssertionError('no splitting circle')
        if undotted:
            return output | (1 << split[0]), output | (1 << split[1])
        return (output,)
    raise AssertionError('a planar saddle must change the number of circles by one')


def reduced_rank(strands: int, word: Iterable[int], *, max_crossings: int | None = 12,
                 max_dimension: int | None = 100_000, check_square: bool = False
                 ) -> dict[str, int]:
    word = validate_word(strands, word)
    n = len(word)
    if max_crossings is not None and n > max_crossings:
        raise CubeLimit('crossing limit exceeded in the exponential cube oracle')
    states: list[tuple[list[int], int, int, int]] = []
    total = 0
    for mask in range(1 << n):
        labels, circles = _components(strands, word, mask)
        mark = labels[0]
        states.append((labels, circles, mark, total))
        total += 1 << (circles - 1)
        if max_dimension is not None and total > max_dimension:
            raise CubeLimit('basis-dimension limit exceeded in the exponential cube oracle')
    columns = [0] * total
    edges = 0
    for mask, (labels, circles, mark, offset) in enumerate(states):
        for crossing in range(n):
            if (mask >> crossing) & 1:
                continue
            other = mask | (1 << crossing)
            other_labels, other_circles, other_mark, other_offset = states[other]
            relation = [set() for _ in range(circles)]
            for first, second in zip(labels, other_labels):
                relation[first].add(second)
            for basis in range(1 << (circles - 1)):
                source_bits = _insert_marked_bit(basis, mark)
                for image in _saddle_images(source_bits, relation, other_circles):
                    target = other_offset + _remove_marked_bit(image, other_mark)
                    columns[offset + basis] ^= 1 << target
                    edges += 1
    if check_square:
        for column in columns:
            square = 0
            remaining = column
            while remaining:
                bit = remaining & -remaining
                square ^= columns[bit.bit_length() - 1]
                remaining ^= bit
            if square:
                raise AssertionError('the cube differential does not square to zero')
    pivots: dict[int, int] = {}
    for column in columns:
        while column:
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = column
                break
            column ^= pivots[pivot]
    return {'crossings': n, 'chain_dimension': total, 'differential_rank': len(pivots),
            'homology_rank': total - 2 * len(pivots), 'saddle_terms': edges}
