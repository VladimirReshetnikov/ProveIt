"""Independent signed-permutation checks of local spectral certificates.

Run with Python 3.8 or newer. Unlimited-precision integers, no dependencies.
Each determinant is recomputed from its entries, without using Schur complements.
"""
from collections import defaultdict

PERIOD = (1, 1, -1, 1, -1, -1, 1, -1)


def shifted_determinant(triangles, adjacency_sign, numerator, denominator):
    """Compute det(numerator I + denominator * adjacency_sign * A)."""
    order = len(triangles) + 2
    totals = {0: 1}
    for row in range(order):
        next_totals = defaultdict(int)
        for used, coefficient in totals.items():
            for column in range(max(0, row - 2), min(order, row + 3)):
                if used & (1 << column):
                    continue
                new_used = used | (1 << column)
                # Later rows can only reach columns >= row - 1.
                inaccessible = (1 << max(0, row - 1)) - 1
                if new_used & inaccessible != inaccessible:
                    continue
                distance = abs(row - column)
                if distance == 0:
                    entry = numerator
                else:
                    sign = 1 if distance == 1 else triangles[min(row, column)]
                    entry = denominator * adjacency_sign * sign
                # Newly introduced inversions are old columns greater than this one.
                inversions = bin(used >> (column + 1)).count('1')
                next_totals[new_used] += coefficient * entry * (-1)**inversions
        totals = next_totals
    return totals[(1 << order) - 1]


def survivors(numerator, denominator, maximum_length):
    states = [()]
    counts = []
    for length in range(1, maximum_length + 1):
        extensions = (word + (sign,) for word in states for sign in (1, -1))
        states = [word for word in extensions
                  if all(shifted_determinant(word, scale, numerator, denominator) > 0
                         for scale in (1, -1))]
        counts.append(len(states))
    print(f'Threshold {numerator}/{denominator}, lengths 1 through {maximum_length}:')
    print(', '.join(map(str, counts)))
    return set(states)


def rotations(length):
    return {tuple(PERIOD[(i+j) % 8] for j in range(length)) for i in range(8)}


def check_short_cyclic_windows():
    """A window belonging to a cyclic word needs a predecessor and a successor."""
    words = survivors(1397, 500, 12)
    counts = [len(words)]
    while True:
        internal = {word[:-1] for word in words} & {word[1:] for word in words}
        retained = {word for word in words if word[:-1] in internal and word[1:] in internal}
        if retained == words:
            break
        words = retained
        counts.append(len(words))
    alternating = {tuple(sign * (-1)**i for i in range(12)) for sign in (1, -1)}
    assert counts == [42, 20, 10]
    assert words == rotations(12) | alternating
    assert len({word[:-1] for word in words}) == 10
    print('Length-12 trimming counts:', counts)
    print('The ten surviving edges form disjoint cycles of lengths eight and two.')


def main():
    check_short_cyclic_windows()
    short = survivors(1397, 500, 27)
    assert short == rotations(27)
    print('The complete 27-letter words are exactly the eight predicted rotations.')
    long = survivors(281, 100, 43)
    assert len(long) == 72
    assert {word[17:26] for word in long} == rotations(9)
    print('The centered 9-letter words are exactly the eight predicted rotations.')


if __name__ == '__main__':
    main()
