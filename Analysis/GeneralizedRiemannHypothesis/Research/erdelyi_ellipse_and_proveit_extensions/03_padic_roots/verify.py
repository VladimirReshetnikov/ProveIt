"""Reproduce the finite examples in the paper; no network or third-party modules."""
from fractions import Fraction
from random import Random
from disk_roots import counts, envelope, modulus


def main():
    for p, expected in [(2, [2, 4, 4, 8, 8]), (3, [3, 9, 9, 10]), (5, [10, 25, 25, 26, 26, 27])]:
        for t, target in zip(range(p + 1, p + 1 + len(expected)), expected):
            found, support = envelope(p, t)
            assert found == target, (p, t, found, target)
            print(f"p={p} t={t} open maximum={found} example={support}")

    rng = Random(159627)
    comparisons = 0
    for p, t in [(2, 4), (2, 9), (3, 7), (3, 9), (5, 8)]:
        for _ in range(12):
            E = rng.sample(range(45), t)
            q = modulus(t, p)
            F = [n + (i + 1) * 50 * q for i, n in enumerate(E)]
            for depth in (None, Fraction(1, p - 1) + Fraction(1, 13), Fraction(3, 2)):
                answer = counts(p, E, depth)
                assert counts(p, E, depth, compress=False) == answer
                assert counts(p, F, depth) == answer
                comparisons += 1
    print(f"Direct and compressed pivot checks: {comparisons} cases")
    examples = [([0, 1, 2, 3, 4, 5], 5), ([0, 7, 14, 1, 8, 2], 14)]
    for E, expected in examples:
        assert counts(7, E)[-1] == expected
    for p, E, F, exact_E, exact_F in [
        (2, [0,1,4,5,8,9,12,13], [0,1,3,4,5,8,9,12], list(range(8)), [*range(7),8]),
        (3, [0,1,2,9,10,11,18,19,20], [0,1,2,5,9,10,11,18,19], list(range(9)), [*range(8),9]),
    ]:
        assert sorted(x % p for x in E) == sorted(x % p for x in F)
        assert counts(p, E, compress=False) == exact_E and counts(p, F, compress=False) == exact_F
        print(f"One-digit insufficiency: p={p} attainable counts {exact_E} vs {exact_F}")
    # Critical boundary: exactly one root inside, all p roots on or inside.
    assert counts(5, [0, 5]) == [0, 1]


if __name__ == "__main__":
    main()
