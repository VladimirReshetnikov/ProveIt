#!/usr/bin/env python3
"""Finite checks for lexicographic well-order and surreal-word constructions.

Run with Python 3; no third-party packages are required.  These exhaustive
finite checks guard the definitions and small cases.  They do not verify the
transfinite proofs, class comprehension, saturation, or cardinal arithmetic.
"""

from itertools import combinations, permutations, product


def compare_signs(left, right):
    """Surreal sign order: at the first difference, - < termination < +."""
    for a, b in zip(left, right):
        if a != b:
            return (a > b) - (a < b)
    if len(left) == len(right):
        return 0
    if len(left) < len(right):
        return -right[len(left)]
    return left[len(right)]


def sign_code(signs):
    """C(x) = (+) concatenated with doubled signs and the terminator (+,-)."""
    return (1,) + tuple(s for s in signs for _ in range(2)) + (1, -1)


def word_code(word):
    return tuple(sign for value in word for sign in sign_code(value))


def compare_words(left, right):
    """Word lexicographic order, with every proper prefix smaller."""
    for a, b in zip(left, right):
        comparison = compare_signs(a, b)
        if comparison:
            return comparison
    return (len(left) > len(right)) - (len(left) < len(right))


def is_prefix(left, right):
    return len(left) <= len(right) and right[:len(left)] == left


def finite_sign_words(max_length):
    return [s for n in range(max_length + 1) for s in product((-1, 1), repeat=n)]


def check_sign_and_word_codes():
    alphabet = finite_sign_words(4)
    codes = {s: sign_code(s) for s in alphabet}
    sign_pairs = 0
    for left, right in combinations(alphabet, 2):
        assert not is_prefix(codes[left], codes[right])
        assert not is_prefix(codes[right], codes[left])
        assert compare_signs(left, right) == compare_signs(codes[left], codes[right])
        sign_pairs += 1
    assert all(code[0] == 1 for code in codes.values())

    # Repeated entries are allowed here: the coding theorem is stronger than
    # its restriction to injective words, which represent well-orders of sets.
    small_alphabet = finite_sign_words(2)
    words = [w for n in range(4) for w in product(small_alphabet, repeat=n)]
    encoded = {w: word_code(w) for w in words}
    assert len(set(encoded.values())) == len(words)
    assert encoded[()] == ()
    assert all(compare_signs((), code) < 0 for w, code in encoded.items() if w)
    word_pairs = 0
    for left, right in combinations(words, 2):
        assert compare_words(left, right) == compare_signs(encoded[left], encoded[right])
        word_pairs += 1
    injective_words = sum(len(set(w)) == len(w) for w in words)
    print("SIGN CODE: PASS")
    print(f"  All {len(alphabet)} sign words of length at most 4; {sign_pairs} pairs.")
    print("  Verified strict order preservation, prefix freedom, and initial +.")
    print("CONCATENATED WORD CODE: PASS")
    print(f"  {len(words)} words of length at most 3 over {len(small_alphabet)} values.")
    print(f"  {word_pairs} pairs; {injective_words} of the words are injective.")
    print("  Verified injectivity, order preservation, and the empty-prefix rule.")


def predecessor_masks(order):
    """For each element x, store the predecessor set as a finite bit mask."""
    result = [0] * len(order)
    preceding = 0
    for value in order:
        result[value] = preceding
        preceding |= 1 << value
    return tuple(result)


def compare_by_predecessors(left, right, left_masks, right_masks):
    difference = 0
    for value, (a, b) in enumerate(zip(left_masks, right_masks)):
        if a != b:
            difference |= 1 << value
    if not difference:
        return 0
    a = next(value for value in left if difference & (1 << value))
    b = next(value for value in right if difference & (1 << value))
    return (a > b) - (a < b)


def adjacency_prediction(left, right):
    """The residual-set criterion for left < right among full enumerations."""
    index = next(i for i, (a, b) in enumerate(zip(left, right)) if a != b)
    a, b = left[index], right[index]
    residual = set(left[index:])
    consecutive = a < b and not any(a < value < b for value in residual)
    largest_left_tail = tuple(sorted(residual - {a}, reverse=True))
    smallest_right_tail = tuple(sorted(residual - {b}))
    adjacent = (
        consecutive
        and left[index + 1:] == largest_left_tail
        and right[index + 1:] == smallest_right_tail
    )
    return adjacent, len(residual)


def check_permutations():
    total_pairs = 0
    total_adjacent = 0
    residual_counts = {}
    for size in range(7):
        orders = list(permutations(range(size)))
        masks = [predecessor_masks(order) for order in orders]
        for index, left in enumerate(orders):
            assert compare_by_predecessors(left, left, masks[index], masks[index]) == 0
            for other_index in range(index + 1, len(orders)):
                right = orders[other_index]
                assert left < right
                assert compare_by_predecessors(left, right, masks[index], masks[other_index]) == -1
                assert compare_by_predecessors(right, left, masks[other_index], masks[index]) == 1
                predicted, residual_size = adjacency_prediction(left, right)
                actual = other_index == index + 1
                assert predicted == actual
                total_pairs += 1
                if actual:
                    total_adjacent += 1
                    residual_counts[residual_size] = residual_counts.get(residual_size, 0) + 1
    print("PREDECESSOR COMPARISON: PASS")
    print("  All permutations of {0,...,n-1}, for n = 0,...,6.")
    print(f"  {total_pairs} unordered distinct pairs, tested in both directions.")
    print("  D = {x : Pred_R(x) != Pred_S(x)}; compare min_R D and min_S D.")
    print("ADJACENCY CRITERION: PASS")
    print(f"  All {total_pairs} pairs; {total_adjacent} actual adjacent pairs.")
    print("  Counts by the size of the residual set after the common prefix:")
    for size, count in sorted(residual_counts.items()):
        print(f"    {size}: {count}")


def main():
    check_sign_and_word_codes()
    check_permutations()
    print("LIMITATIONS")
    print("  Exhaustive only on the finite domains stated above.")
    print("  No transfinite, infinite-cardinal, saturation, or class-theoretic claim")
    print("  is established by this script; those require the article's proofs.")


if __name__ == "__main__":
    main()
