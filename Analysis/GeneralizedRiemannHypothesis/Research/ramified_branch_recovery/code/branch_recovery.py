#!/usr/bin/env python3
"""Exact contact-tree capacities and a reference decoder (Python 3.10+, stdlib).

All computations are integer or finite-field computations; no numerical tolerance
is used. See paper.tex for proofs and for the distinction between recovery of a
total jet and recovery of the entire formal power series.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from math import inf
from typing import Callable, Iterable


@dataclass(frozen=True)
class Node:
    """A contact-tree node. length is the increment above its parent's contact.

    A leaf has length 0 and one label. At an internal node, the cumulative
    contact is the minimum pairwise contact of the descendant leaves.
    """
    length: int
    labels: tuple[int, ...]
    children: tuple["Node", ...] = ()

    @property
    def size(self) -> int:
        return len(self.labels)


def contact_tree(labels: Iterable[int], contact: Callable[[int, int], int],
                 parent: int = 0) -> Node:
    labels = tuple(sorted(labels))
    if not labels:
        raise ValueError("The original branch set must be nonempty")
    if len(labels) == 1:
        return Node(0, labels)
    level = min(contact(a, b) for a, b in combinations(labels, 2))
    if level < parent:
        raise ValueError("Invalid contact hierarchy")
    groups: list[list[int]] = []
    for a in labels:
        for group in groups:
            if contact(a, group[0]) > level:
                group.append(a)
                break
        else:
            groups.append([a])
    if len(groups) < 2:
        raise ValueError("Invalid contact partition")
    # Check the proposed ultrametric partition, rather than silently assuming it.
    for i, group in enumerate(groups):
        for a, b in combinations(group, 2):
            if contact(a, b) <= level:
                raise ValueError("Contacts fail the ultrametric inequality")
        for other in groups[i + 1:]:
            if any(contact(a, b) != level for a in group for b in other):
                raise ValueError("Contacts fail the ultrametric inequality")
    return Node(level - parent, labels,
                tuple(contact_tree(g, contact, level) for g in groups))


def greedy_spectrum(labels: Iterable[int], contact: Callable[[int, int], int],
                    limit: int | None = None) -> tuple[list[int], list[int]]:
    """Direct greedy computation, independent of the tree recurrence."""
    remaining = set(labels)
    chosen: list[int] = []
    spectrum: list[int] = []
    if limit is None:
        limit = len(remaining)
    while remaining and len(chosen) < limit:
        cost, a = min((sum(contact(a, b) for b in chosen), a)
                      for a in remaining)
        remaining.remove(a)
        chosen.append(a)
        spectrum.append(cost)
    return chosen, spectrum


def tree_spectrum(node: Node, retained: frozenset[int] | None = None) -> list[int]:
    if retained is None:
        retained = frozenset(node.labels)
    if not node.children:
        return [0] if node.labels[0] in retained else []
    merged = sorted(x for child in node.children
                    for x in tree_spectrum(child, retained))
    return [j * node.length + x for j, x in enumerate(merged)]


@lru_cache(maxsize=None)
def capacity(node: Node, r: int, threshold: int) -> int:
    """max |S| with the r-th residual factorial >= threshold (0-based).

    Missing factorials are +infinity. This is the outer adversarial pruning
    optimization; it is not Bhargava's operation of removing terms in a product.
    """
    if r < 0:
        raise ValueError("r must be nonnegative")
    if threshold <= 0 or r >= node.size:
        return node.size
    if not node.children:
        return 0  # r=0, threshold>0
    child_threshold = threshold - r * node.length
    if child_threshold <= 0:
        return node.size
    dp = [0] + [-10**9] * r
    for child in node.children:
        dp = [max(dp[b - k] + capacity(child, k, child_threshold)
                  for k in range(b + 1)) for b in range(r + 1)]
    return max(dp)


def capacity_witness(node: Node, r: int, threshold: int) -> tuple[int, ...]:
    """Backtrack an extremizing retained set for capacity()."""
    if threshold <= 0 or r >= node.size:
        return node.labels
    if not node.children:
        return ()
    child_threshold = threshold - r * node.length
    if child_threshold <= 0:
        return node.labels
    # Entries hold both maximum capacity and one allocation of the rank budget.
    dp: list[tuple[int, tuple[int, ...]] | None] = [(0, ())] + [None] * r
    for child in node.children:
        nxt = []
        for budget in range(r + 1):
            choices = []
            for k in range(budget + 1):
                prior = dp[budget - k]
                if prior is not None:
                    choices.append((prior[0] + capacity(child, k, child_threshold),
                                    prior[1] + (k,)))
            nxt.append(max(choices) if choices else None)
        dp = nxt
    best = max(x for x in dp if x is not None)
    answer = tuple(sorted(a for child, k in zip(node.children, best[1])
                          for a in capacity_witness(child, k, child_threshold)))
    assert len(answer) == capacity(node, r, threshold)
    return answer


def relative_distance(node: Node, d: int, n: int) -> int:
    if d < 1 or n < 0:
        raise ValueError("d>=1 and n>=0 required")
    return node.size - capacity(node, d - 1, n)


def recovery_cutoff(node: Node, d: int, errors: int = 0, erasures: int = 0):
    if min(errors, erasures) < 0:
        raise ValueError("Nonnegative error and erasure budgets required")
    if node.size - 2 * errors - erasures < d:
        return inf
    hi = 1
    while relative_distance(node, d, hi) <= 2 * errors + erasures:
        hi *= 2
    lo = 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if relative_distance(node, d, mid) > 2 * errors + erasures:
            hi = mid
        else:
            lo = mid
    return hi


def vp(a: int, p: int) -> int:
    if not a:
        raise ValueError("Contact of a label with itself is not defined")
    a = abs(a)
    r = 0
    while a % p == 0:
        a //= p
        r += 1
    return r


def lt_contact(a: int, b: int, p: int = 2) -> int:
    """Integer directions over Q_p, whose residue-field size is p."""
    return p ** vp(a - b, p)


def f2_mul(a: int, b: int, n: int) -> int:
    """Multiply polynomials over F2 modulo X^n, encoded as bitsets."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        b >>= 1
    return result & ((1 << n) - 1)


def multiplicative_branch(b: int, n: int) -> int:
    """(1+X)^b-1 modulo (2,X^n), using Lucas' binary criterion."""
    if b < 0:
        raise ValueError("This reference implementation uses nonnegative labels")
    return sum(1 << i for i in range(1, min(b + 1, n)) if (i & b) == i)


def monomials(n: int) -> list[tuple[int, int]]:
    return [(degree - j, j) for degree in range(n) for j in range(degree + 1)]


def evaluation_rows(labels: Iterable[int], n: int):
    """Rows of substitution on all monomials of total degree < n over F2."""
    mons = monomials(n)
    blocks = {}
    for b in labels:
        u = multiplicative_branch(b, n)
        powers = [1]
        for _ in range(1, n):
            powers.append(f2_mul(powers[-1], u, n))
        rows = [0] * n
        for col, (i, j) in enumerate(mons):
            image = (powers[j] << i) & ((1 << n) - 1)
            while image:
                bit = image & -image
                rows[bit.bit_length() - 1] |= 1 << col
                image ^= bit
        blocks[b] = rows
    return mons, blocks


def row_basis(rows: Iterable[int]) -> dict[int, int]:
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row
                break
            row ^= pivots[p]
    return pivots


def in_row_span(row: int, basis: dict[int, int]) -> bool:
    while row:
        p = row.bit_length() - 1
        if p not in basis:
            return False
        row ^= basis[p]
    return True


def jet_recoverable_by_matrix(labels: Iterable[int], d: int, n: int) -> bool:
    if n < d:
        return False
    _, blocks = evaluation_rows(labels, n)
    basis = row_basis(row for block in blocks.values() for row in block)
    return all(in_row_span(1 << j, basis) for j in range(d * (d + 1) // 2))


def solve_f2(equations: Iterable[tuple[int, int]], variables: int) -> int | None:
    """One exact solution; free variables are set to zero. None=inconsistent."""
    pivots: dict[int, tuple[int, int]] = {}
    for row, rhs in equations:
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = (row, rhs)
                break
            old, value = pivots[p]
            row ^= old
            rhs ^= value
        else:
            if rhs:
                return None
    solution = 0
    for p in sorted(pivots):
        row, rhs = pivots[p]
        value = rhs ^ ((row & solution).bit_count() & 1)
        solution |= value << p
    assert solution < (1 << variables)
    return solution


def encode_f2(polynomial_bits: int, blocks: dict[int, list[int]]) -> dict[int, int]:
    return {b: sum((((row & polynomial_bits).bit_count() & 1) << k)
                   for k, row in enumerate(rows)) for b, rows in blocks.items()}


def decode_f2(received: dict[int, int], d: int, n: int, errors: int,
              check_all: bool = False) -> dict:
    """Reference decoder by guessing erroneous blocks and solving linear systems.

    Missing keys represent declared erasures. The exact relative-distance guard
    is enforced on the actual retained configuration. This routine is exponential
    in the block-error budget; it makes no efficiency claim. It is a guaranteed
    unique-jet decoder under that guard, not a general list decoder.
    """
    labels = tuple(sorted(received))
    if not labels or min(labels) < 0 or d < 1 or n < 0 or errors < 0:
        raise ValueError("Nonempty nonnegative labels, d>=1, n>=0, errors>=0 required")
    if any(value < 0 or value >= (1 << n) for value in received.values()):
        raise ValueError("Each received block must have exactly n bits or fewer")
    actual_tree = contact_tree(labels, lt_contact)
    if relative_distance(actual_tree, d, n) <= 2 * errors:
        raise ValueError("The exact distance does not guarantee unique jet recovery")
    mons, blocks = evaluation_rows(labels, n)
    jet_mask = (1 << (d * (d + 1) // 2)) - 1
    candidate_jets = set()
    consistent = []
    systems = 0
    for guessed_bad in combinations(labels, errors):
        bad = set(guessed_bad)
        equations = ((row, (received[b] >> k) & 1)
                     for b in labels if b not in bad
                     for k, row in enumerate(blocks[b]))
        systems += 1
        answer = solve_f2(equations, len(mons))
        if answer is None:
            continue
        candidate_jets.add(answer & jet_mask)
        consistent.append(guessed_bad)
        if not check_all:
            break
    return {"systems_examined": systems,
            "consistent_error_location_sets": consistent,
            "candidate_jet_bitsets": sorted(candidate_jets),
            "monomial_order": mons[:d * (d + 1) // 2]}


if __name__ == "__main__":
    tree = contact_tree(range(16), lt_contact)
    print("16 binary multiplicative branches; total jet degree < 6")
    for t in range(6):
        print(f"errors={t}: exact coefficient cutoff={recovery_cutoff(tree, 6, t)}")
