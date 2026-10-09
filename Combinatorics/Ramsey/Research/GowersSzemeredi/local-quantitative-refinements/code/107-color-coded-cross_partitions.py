#!/usr/bin/env python3
"""Exact finite constructions used in the accompanying research manuscript.

Standard library only.  This module is an implementation, not a formal proof.
Fields supported computationally: prime fields and F_4 = F_2[a]/(a^2+a+1).
All theorem statements in the article allow every prime power q > 2.

Arms are labelled 0,...,s-1; -1 is the *separate* zero-block symbol.
An affine line is stored in an orthant by its arms, anchor, and direction.
The construction is intentionally finite/enumerative, not a complexity claim.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import combinations, product
from math import comb, isqrt
from typing import Callable, Hashable, Iterable, TypeVar

Vertex = TypeVar('Vertex', bound=Hashable)
Right = TypeVar('Right', bound=Hashable)
Word = tuple[int, ...]


@dataclass(frozen=True)
class FiniteField:
    q: int

    def __post_init__(self) -> None:
        if self.q < 2:
            raise ValueError('Field size must be at least two.')
        if self.q != 4 and any(self.q % d == 0 for d in range(2, isqrt(self.q) + 1)):
            raise ValueError('This checker supports prime fields and F_4 only.')

    def add(self, x: int, y: int) -> int:
        return x ^ y if self.q == 4 else (x + y) % self.q

    def mul(self, x: int, y: int) -> int:
        if self.q != 4:
            return x * y % self.q
        out = 0
        while y:
            if y & 1:
                out ^= x
            y >>= 1
            x <<= 1
            if x & 4:
                x ^= 7
        return out

    def inv(self, x: int) -> int:
        if x == 0:
            raise ZeroDivisionError('Zero has no multiplicative inverse.')
        for y in range(1, self.q):
            if self.mul(x, y) == 1:
                return y
        raise ArithmeticError('Invalid finite field implementation.')

    def div(self, x: int, y: int) -> int:
        return self.mul(x, self.inv(y))

    def prod(self, xs: Iterable[int]) -> int:
        result = 1
        for x in xs:
            result = self.mul(result, x)
        return result


def ceildiv(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError('Positive denominator required.')
    return -(-a // b)


def full_matching(left: Iterable[Vertex], neighbors: Callable[[Vertex], Iterable[Right]]) -> dict[Vertex, Right]:
    """Saturate the left side by exact augmenting paths; reject if impossible."""
    left = list(left)
    if len(set(left)) != len(left):
        raise ValueError('Duplicate left vertices.')
    ml: dict[Vertex, Right] = {}
    mr: dict[Right, Vertex] = {}
    cache: dict[Vertex, tuple[Right, ...]] = {}
    for root in left:
        queue = deque([root])
        reached_left = {root}
        parent: dict[Right, Vertex] = {}
        endpoint = None
        while queue and endpoint is None:
            u = queue.popleft()
            if u not in cache:
                cache[u] = tuple(neighbors(u))
            for v in cache[u]:
                if v in parent:
                    continue
                parent[v] = u
                if v not in mr:
                    endpoint = v
                    break
                nxt = mr[v]
                if nxt not in reached_left:
                    reached_left.add(nxt)
                    queue.append(nxt)
        if endpoint is None:
            raise ValueError('No left-saturating matching exists for the supplied graph.')
        v = endpoint
        while True:
            u = parent[v]
            previous = ml.get(u)
            ml[u] = v
            mr[v] = u
            if previous is None:
                break
            v = previous
    if len(ml) != len(left) or len(set(ml.values())) != len(left):
        raise ArithmeticError('Internal matching invariant failed.')
    return ml


def words_for_zero_set(s: int, m: int, zeros: tuple[int, ...]) -> Iterable[Word]:
    zero_set = set(zeros)
    positions = [i for i in range(m) if i not in zero_set]
    for labels in product(range(s), repeat=len(positions)):
        word = [-1] * m
        for i, label in zip(positions, labels):
            word[i] = label
        yield tuple(word)


def layer(s: int, m: int, zero_count: int) -> list[Word]:
    return [u for z in combinations(range(m), zero_count) for u in words_for_zero_set(s, m, z)]


def extensions(u: Word, s: int) -> Iterable[Word]:
    zeros = [i for i, a in enumerate(u) if a < 0]
    for labels in product(range(s), repeat=len(zeros)):
        w = list(u)
        for i, a in zip(zeros, labels):
            w[i] = a
        yield tuple(w)


def support_chains(s: int, m: int, head_zero_count: int) -> dict[Word, list[Word]]:
    """Partition words with >= head_zero_count zeros into nested chains."""
    if not 1 <= head_zero_count <= m or m > s:
        raise ValueError('The proved chain construction requires 1 <= head zeros <= m <= s.')
    predecessor: dict[Word, Word] = {}
    for zeros in range(m, head_zero_count, -1):
        left = layer(s, m, zeros)
        def adjacent(u: Word) -> Iterable[Word]:
            for i, a in enumerate(u):
                if a == -1:
                    for new_arm in range(s):
                        v = list(u)
                        v[i] = new_arm
                        yield tuple(v)
        matched = full_matching(left, adjacent)
        for u, v in matched.items():
            if v in predecessor:
                raise ArithmeticError('Two predecessors in a support chain.')
            predecessor[v] = u
    chains = {}
    for head in layer(s, m, head_zero_count):
        chain = [head]
        while chain[-1] in predecessor:
            chain.append(predecessor[chain[-1]])
        chains[head] = chain
    flattened = [u for chain in chains.values() for u in chain]
    expected = sum(comb(m, z) * s**(m-z) for z in range(head_zero_count, m+1))
    if len(flattened) != expected or len(set(flattened)) != expected:
        raise ArithmeticError('Support-chain coverage failed.')
    return chains


def line_record(arms: Word, anchor: list[int], direction: list[int]) -> dict:
    return {'arms': list(arms), 'anchor': anchor, 'direction': direction}


def anchors(u: Word, q: int) -> Iterable[list[int]]:
    outside = [i for i, a in enumerate(u) if a >= 0]
    for values in product(range(1, q), repeat=len(outside)):
        point = [0] * len(u)
        for i, value in zip(outside, values):
            point[i] = value
        yield point


def pack_chain(chain: list[Word], orthant: Word, field: FiniteField) -> list[dict]:
    """Prefix-ratio line packing; every line has one boundary point."""
    if field.q <= 2 or sum(a < 0 for a in chain[0]) < 2:
        raise ValueError('Prefix packing needs q > 2 and at least two initial zeros.')
    order = [i for i, a in enumerate(chain[0]) if a < 0]
    previous = set(order)
    for u in chain[1:]:
        now = {i for i, a in enumerate(u) if a < 0}
        added = now - previous
        if len(added) != 1 or not previous < now:
            raise ValueError('Not a nested one-step support chain.')
        order.extend(sorted(added))
        previous = now
    output = []
    for u in chain:
        z = sum(a < 0 for a in u)
        direction = [0] * len(u)
        direction[order[0]] = 1
        for i in order[1:z-1]:
            direction[i] = 2   # second nonzero field element, distinct from 1
        direction[order[z-1]] = 1
        for anchor in anchors(u, field.q):
            output.append(line_record(orthant, anchor, direction.copy()))
    return output


def construct_simple(q: int, s: int, m: int) -> dict:
    """Exact optimizer when m/s + binom(m,2)/s^2 <= 1."""
    field = FiniteField(q)
    if q <= 2 or s < 2 or m < 1 or m * s + comb(m, 2) > s*s:
        raise ValueError('The elementary exact-region hypothesis fails.')
    if m == 1:
        u = (-1,)
        return {'q': q, 's': s, 'm': m, 'method': 'simple',
                'lines': [line_record((0,), [0], [1])]}
    chains = support_chains(s, m, 2)
    one_zero = layer(s, m, 1)
    matched = full_matching(one_zero + list(chains), lambda u: extensions(u, s))
    lines = []
    for u in one_zero:
        z = u.index(-1)
        direction = [int(i == z) for i in range(m)]
        for anchor in anchors(u, q):
            lines.append(line_record(matched[u], anchor, direction.copy()))
    for head, chain in chains.items():
        lines.extend(pack_chain(chain, matched[head], field))
    return {'q': q, 's': s, 'm': m, 'method': 'simple', 'lines': lines,
            'routing_heads': len(matched), 'tail_chains': len(chains)}


def color_classes(m: int, z: int) -> list[tuple[tuple[int, ...], list[tuple[int, ...]]]]:
    """Small deterministic perfect-hash family by exhaustive greedy covering.

    This is for finite checks, not the asymptotic hash-family implementation.
    """
    if not 1 <= z <= m:
        raise ValueError('Require 1 <= z <= m.')
    uncovered = set(combinations(range(m), z))
    if z == 1:
        return [((0,) * m, sorted(uncovered))]
    if z**(m-1) > 1_000_000:
        raise ValueError('Exhaustive coloring guard exceeded.')
    candidates = []
    for tail in product(range(z), repeat=m-1):
        h = (0,) + tail
        covered = {Z for Z in uncovered if len({h[i] for i in Z}) == z}
        if covered:
            candidates.append((h, covered))
    classes = []
    while uncovered:
        h, covered = max(candidates, key=lambda item: len(item[1] & uncovered))
        assigned = sorted(covered & uncovered)
        if not assigned:
            raise ArithmeticError('Perfect-hash coverage failed.')
        classes.append((h, assigned))
        uncovered.difference_update(assigned)
    return classes


def syndrome(x: tuple[int, ...] | list[int], coloring: tuple[int, ...], z: int,
             field: FiniteField) -> tuple[int, ...]:
    products = [field.prod(x[i] for i in range(len(x)) if coloring[i] == c) for c in range(z)]
    return tuple(field.div(products[c], products[-1]) for c in range(z-1))


def pack_syndrome(u: Word, orthant: Word, coloring: tuple[int, ...],
                  eta: tuple[int, ...], field: FiniteField) -> list[dict]:
    z = len(eta) + 1
    zeros = [i for i, arm in enumerate(u) if arm < 0]
    if len(zeros) != z or len({coloring[i] for i in zeros}) != z:
        raise ValueError('The zero set is not rainbow for the supplied coloring.')
    missing = {coloring[i]: i for i in zeros}
    output = []
    for anchor in anchors(u, field.q):
        A = [field.prod(anchor[i] for i in range(len(u))
                        if u[i] >= 0 and coloring[i] == c) for c in range(z)]
        direction = [0] * len(u)
        direction[missing[z-1]] = 1
        for c in range(z-1):
            direction[missing[c]] = field.mul(eta[c], field.div(A[z-1], A[c]))
        output.append(line_record(orthant, anchor, direction))
    return output


def construct_colored(q: int, s: int, m: int, R: int) -> dict:
    """Construct using exact color-class residue budgets, when they fit."""
    field = FiniteField(q)
    if q <= 2 or not 1 <= R < m <= s:
        raise ValueError('Require q > 2 and 1 <= R < m <= s.')
    t = q - 1
    groups = []
    next_residue = 0
    for z in range(1, R+1):
        for coloring, sets in color_classes(m, z):
            needed = ceildiv(len(sets), (s*t)**(z-1))
            residues = tuple(range(next_residue, next_residue + needed))
            next_residue += needed
            groups.append((z, coloring, sets, residues))
    tail_needed = ceildiv(comb(m, R+1), s**R)
    tail_residues = tuple(range(next_residue, next_residue + tail_needed))
    total_budget = next_residue + tail_needed
    if total_budget > s:
        raise ValueError(f'Color budget {total_budget} exceeds {s} arms.')
    lines = []
    group_stats = []
    for z, coloring, sets, residues in groups:
        etas = list(product(range(1, q), repeat=z-1))
        residue_set = set(residues)
        left = [u for Z in sets for u in words_for_zero_set(s, m, Z)]
        def adjacent(u: Word) -> Iterable[tuple[Word, tuple[int, ...]]]:
            for w in extensions(u, s):
                if sum(w) % s in residue_set:
                    for eta in etas:
                        yield w, eta
        matched = full_matching(left, adjacent)
        for u, (w, eta) in matched.items():
            lines.extend(pack_syndrome(u, w, coloring, eta, field))
        group_stats.append({'zero_count': z, 'coloring': list(coloring),
                            'zero_sets': [list(Z) for Z in sets],
                            'residues': list(residues), 'matched_words': len(matched)})
    chains = support_chains(s, m, R+1)
    tail_residue_set = set(tail_residues)
    def adjacent_tail(u: Word) -> Iterable[Word]:
        return (w for w in extensions(u, s) if sum(w) % s in tail_residue_set)
    tail_matching = full_matching(chains, adjacent_tail)
    for head, chain in chains.items():
        lines.extend(pack_chain(chain, tail_matching[head], field))
    return {'q': q, 's': s, 'm': m, 'R': R, 'method': 'colored',
            'residue_budget': total_budget, 'groups': group_stats,
            'tail_residues': list(tail_residues), 'tail_chains': len(chains), 'lines': lines}
