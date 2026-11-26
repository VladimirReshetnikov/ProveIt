#!/usr/bin/env python3
"""Check the residue-ball optimization and the second-precision formula."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement

from check_branch_precision import companion_threshold, valuation


@lru_cache(maxsize=None)
def pole(prime, residue_size, precision, depths):
    return companion_threshold(prime, residue_size, precision, depths)


def common_cutoff(prime, precision, points):
    return 1 + max(
        pole(prime, prime, precision,
             tuple(sorted(valuation(b-c, prime) for c in points if c != b)))
        for b in points
    )


def digit_profile(size, prime, ball_depth):
    # Differences from the zeroth point in a balanced digit set realize
    # all the maximal cumulative occupancies at once.
    return tuple(sorted(ball_depth + valuation(i, prime) for i in range(1, size)))


def main():
    configurations = 0
    for prime, reservoir_size in [(2, 8), (3, 9)]:
        for ball_depth in [0, 1]:
            points = [i * prime**ball_depth for i in range(reservoir_size)]
            for size in range(1, reservoir_size+1):
                for precision in [1, 2, 3, 4]:
                    observed = [common_cutoff(prime, precision, choice)
                                for choice in combinations(points, size)]
                    configurations += len(observed)
                    predicted = 1 + pole(prime, prime, precision,
                                         digit_profile(size, prime, ball_depth))
                    assert min(observed) == predicted
                    assert common_cutoff(prime, precision, points[:size]) == predicted
    print("Finite residue-ball designs tested:", configurations)

    profiles = 0
    for prime, q, max_depth in [(2, 2, 4), (3, 3, 3), (2, 4, 2)]:
        for length in range(5):
            for depths in combinations_with_replacement(range(max_depth+1), length):
                counts = Counter(depths)
                correction = max(((q-1)*q**(h-1) for h in counts
                                  if h >= 1 and counts[h] % prime), default=0)
                predicted = sum(q**h for h in depths) + correction
                assert pole(prime, q, 2, depths) == predicted
                profiles += 1
    print("Second-precision contact profiles tested:", profiles)
    for precision in range(1, 11):
        assert common_cutoff(2, precision, range(8)) == 2*precision+11
        assert common_cutoff(2, precision, range(0, 16, 2)) == 4*precision+21
    print("Eight-direction optimal cutoffs for r=1 through 10 confirmed.")
    print("PASS")


if __name__ == "__main__":
    main()
