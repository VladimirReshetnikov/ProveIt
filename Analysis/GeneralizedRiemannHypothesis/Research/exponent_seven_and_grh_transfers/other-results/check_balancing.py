"""Check the balanced, Galois-stable extremizers for dyadic high shells.
Validates every possible even degree on levels 3 through 10. Also exhausts
all Galois-stable subsets up through level 5 as an independent optimum test.
"""
from fractions import Fraction
from itertools import combinations
from math import inf


def loss_for_marks(marks, units, denom):
    """Minimum normalized excess at unmarked test points."""
    missing = set(units).difference(marks)
    if not missing:
        return inf
    return min(Fraction(sum(((abs(a-b) & -abs(a-b))-1) for b in marks), denom)
               for a in missing)


def best_bound(level, count):
    denom = 1 << (level-1)
    if count == denom:
        return inf
    return Fraction(sum((1 << (i-1)) * (count // (1 << (i-1)))
                        for i in range(1, level)), denom)


def main():
    total = exhaustive = 0
    for level in range(3, 11):
        modulus = 1 << level
        denom = modulus // 2
        units = list(range(1, modulus, 2))
        for c in (modulus-1, denom-1):
            pairs = [(a, a*c % modulus) for a in range(1, modulus, 4)]
            assert set(a for pair in pairs for a in pair) == set(units)
            for pairs_used in range(len(pairs)+1):
                balanced = {a for pair in pairs[:pairs_used] for a in pair}
                target = best_bound(level, 2*pairs_used)
                assert loss_for_marks(balanced, units, denom) == target
                total += 1
                if level <= 5:
                    value = max(loss_for_marks({a for pair in sub for a in pair}, units, denom)
                                for sub in combinations(pairs, pairs_used))
                    assert value == target
                    exhaustive += 1
    print(f'Verified {total} balanced constructions at shells 3 through 10.')
    print(f'Exhaustively maximized {exhaustive} degree/involution cases at shells 3 through 5.')


if __name__ == '__main__':
    main()
