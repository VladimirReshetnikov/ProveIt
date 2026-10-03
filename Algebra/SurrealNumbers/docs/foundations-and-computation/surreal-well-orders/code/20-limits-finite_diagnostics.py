#!/usr/bin/env python3
"""Finite diagnostics accompanying the surreal well-order article.

These checks verify finite first-difference mechanisms and the sign-word
encoder. They do not verify any transfinite or class-theoretic theorem.
Only the Python standard library is used. Run without Python's -O flag.
"""

from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import argparse
import json


def sign(value):
    return (value > 0) - (value < 0)


def first_difference(left, right):
    if left == right:
        return None
    for a, b in zip(left, right):
        if a != b:
            return a, b
    raise ValueError("Expected exhaustive words on the same carrier")


def finite_sign_value(word):
    """Evaluate a finite surreal sign expansion as an exact dyadic."""
    if not word:
        return Fraction(0)
    total = Fraction(word[0])
    step = Fraction(1)
    switched = False
    for digit in word[1:]:
        if switched or digit != word[0]:
            switched = True
            step /= 2
        total += digit * step
    return total


def encode_entry(word):
    return tuple(d for digit in word for d in (digit, digit)) + (-1, 1)


def encode_dictionary_word(word):
    return tuple(d for entry in word for d in (1,) + encode_entry(entry))


def compare_words(left, right):
    for a, b in zip(left, right):
        av, bv = finite_sign_value(a), finite_sign_value(b)
        if av != bv:
            return sign(av - bv)
    return sign(len(left) - len(right))


def run(max_carrier=5):
    if not __debug__:
        raise RuntimeError("Run without optimized Python; assertions are checks")
    counts = {"permutation_pairs": 0, "decisive_pair_restrictions": 0,
              "nested_witness_monotonicity": 0, "dyadic_word_pairs": 0}
    for n in range(2, max_carrier + 1):
        all_permutations = list(permutations(range(n)))
        subsets = [frozenset(i for i in range(n) if mask & (1 << i))
                   for mask in range(1 << n)]
        nested = [(i, j) for i, y in enumerate(subsets)
                  for j, z in enumerate(subsets) if y <= z]
        restrictions = {
            p: [tuple(x for x in p if x in subset) for subset in subsets]
            for p in all_permutations
        }
        for left, right in combinations(all_permutations, 2):
            counts["permutation_pairs"] += 1
            a, b = first_difference(left, right)
            left_pos = {x: i for i, x in enumerate(left)}
            right_pos = {x: i for i, x in enumerate(right)}
            witnesses = [first_difference(l, r)
                         for l, r in zip(restrictions[left], restrictions[right])]
            for subset, witness in zip(subsets, witnesses):
                if a in subset and b in subset:
                    assert witness == (a, b), (left, right, subset, witness)
                    counts["decisive_pair_restrictions"] += 1
            for i, j in nested:
                old = witnesses[i]
                if old is None:
                    continue
                new = witnesses[j]
                assert new is not None
                assert left_pos[new[0]] <= left_pos[old[0]]
                assert right_pos[new[1]] <= right_pos[old[1]]
                counts["nested_witness_monotonicity"] += 1

    entries = [tuple(digits) for size in range(4)
               for digits in product((-1, 1), repeat=size)]
    words = [tuple(es) for size in range(3)
             for es in product(entries, repeat=size)]
    encoded_values = {w: finite_sign_value(encode_dictionary_word(w))
                      for w in words}
    for left, right in combinations(words, 2):
        actual = sign(encoded_values[left] - encoded_values[right])
        expected = compare_words(left, right)
        assert actual == expected, (left, right, actual, expected)
        counts["dyadic_word_pairs"] += 1

    p, q = (0, 2, 1), (1, 0, 2)
    y = {1, 2}
    py = tuple(x for x in p if x in y)
    qy = tuple(x for x in q if x in y)
    assert p < q and py > qy
    return {
        "status": "PASS",
        "max_finite_carrier": max_carrier,
        "counts": counts,
        "word_encoder": {"coefficient_sign_length_at_most": 3,
                         "dictionary_word_length_at_most": 2,
                         "words": len(words),
                         "comparison": "independent exact dyadic evaluation"},
        "restriction_reversal": {"left": p, "right": q,
                                 "restricted_left": py, "restricted_right": qy},
        "scope": "Finite operational diagnostics only; no transfinite, cardinal, "
                 "class recursion, automorphism or model-theoretic theorem is "
                 "machine-verified by these checks."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-carrier", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 2 <= args.max_carrier <= 6:
        parser.error("--max-carrier must be between 2 and 6")
    result = run(args.max_carrier)
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
