#!/usr/bin/env python3
"""Reproduce the article's finite examples using only the Python standard library.

Run: python3 examples.py
These computations concern finite illustrations; the article supplies the proofs
for infinite sets and proper classes.
"""

from collections import Counter
from dataclasses import dataclass
from itertools import combinations, permutations, product


TABLE_SCAN = ((0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1))
PAIR_SCAN = tuple(combinations(range(3), 2))


def display(word):
    return "".join(map(str, word))


def compare(left, right):
    return (left > right) - (left < right)


def inverse(word):
    return tuple(word.index(label) for label in range(len(word)))


def table(word):
    rank = inverse(word)
    return tuple(int(rank[a] < rank[b]) for a, b in TABLE_SCAN)


def restriction(word, labels):
    return tuple(label for label in word if label in labels)


@dataclass
class FiniteOrder:
    word: tuple
    predecessors: dict
    prefix_relations: dict

    @classmethod
    def from_word(cls, word):
        relation = frozenset(combinations(word, 2))
        predecessors = {
            x: frozenset(a for a, b in relation if b == x) for x in word
        }
        prefix_relations = {
            x: frozenset(
                (a, b)
                for a, b in relation
                if a in predecessors[x] and b in predecessors[x]
            )
            for x in word
        }
        return cls(word, predecessors, prefix_relations)


def raw_relation_compare(left, right):
    """Compare through common labelled predecessor relations, without ranking.

    A label belongs to the common prefix precisely when its predecessor set
    and the relation induced on that set agree in both orders.
    """
    assert set(left.word) == set(right.word)
    common = {
        x
        for x in left.word
        if left.predecessors[x] == right.predecessors[x]
        and left.prefix_relations[x] == right.prefix_relations[x]
    }
    remaining = set(left.word) - common
    if not remaining:
        return 0
    next_left = [x for x in remaining if left.predecessors[x] <= common]
    next_right = [x for x in remaining if right.predecessors[x] <= common]
    assert len(next_left) == len(next_right) == 1
    return compare(next_left[0], next_right[0])


def longest_boolean_chain(vectors):
    """Dynamic programming in the coordinatewise order on the Boolean cube."""
    lengths = {}
    for vector in sorted(vectors, key=lambda v: (sum(v), v)):
        lower_lengths = [
            length
            for lower, length in lengths.items()
            if all(a <= b for a, b in zip(lower, vector))
        ]
        lengths[vector] = 1 + max(lower_lengths, default=0)
    return max(lengths.values())


def main():
    words = list(permutations(range(3)))
    print("Three lexicographic comparisons on labels 0 < 1 < 2")
    print("Table scan: (0,1), (0,2), (1,0), (1,2), (2,0), (2,1).")
    print("A table bit is 1 when the first label precedes the second.")
    print("Enumeration  Inverse ranks  Relation table")
    for word in words:
        print(f"{display(word):11}  {display(inverse(word)):13}  {display(table(word))}")
    print("Enumeration order: " + " < ".join(map(display, words)))
    print("Inverse-rank order: " + " < ".join(map(display, sorted(words, key=inverse))))
    print("Relation-table order: " + " < ".join(map(display, sorted(words, key=table))))

    left, right = (0, 2, 1), (1, 0, 2)
    left_restricted = restriction(left, {1, 2})
    right_restricted = restriction(right, {1, 2})
    assert left < right and left_restricted > right_restricted
    print("\nRestriction reverses comparison: 021 < 102, but 21 > 12 on {1,2}.")

    def relabel(word):
        return tuple({0: 1, 1: 0, 2: 2}[x] for x in word)

    assert all(relabel(relabel(word)) == word for word in words)
    assert all(relabel(word) != word for word in words)
    assert (0, 1, 2) < (1, 0, 2)
    assert relabel((0, 1, 2)) > relabel((1, 0, 2))
    print("The relabeling (0 1) exchanges 012 and 102, reverses their comparison,")
    print("and applying it twice returns every enumeration to itself.")

    chain_lengths = []
    for flips in product((0, 1), repeat=3):
        vectors = set()
        for word in words:
            rank = inverse(word)
            vector = tuple(
                int(rank[a] < rank[b]) ^ flip
                for (a, b), flip in zip(PAIR_SCAN, flips)
            )
            vectors.add(vector)
        assert len(vectors) == 6
        length = longest_boolean_chain(vectors)
        assert length <= 4 < 6
        chain_lengths.append(length)
    counts = Counter(chain_lengths)
    assert counts == Counter({4: 6, 2: 2})
    print("\nAll eight choices of orders on the three pair-restriction spaces checked.")
    print("The longest coordinatewise chain has length 4 in six choices and 2 in two.")
    print("None can accommodate all six permutations as a monotone chain.")

    for size in range(6):
        orders = [FiniteOrder.from_word(word) for word in permutations(range(size))]
        for left_order, right_order in product(orders, repeat=2):
            assert raw_relation_compare(left_order, right_order) == compare(
                left_order.word, right_order.word
            )
    print("\nRaw common-prefix relation comparison agrees with enumeration lexicography")
    print("for every pair of permutations on carriers of sizes 0 through 5.")
    print("All finite checks passed.")


if __name__ == "__main__":
    main()
