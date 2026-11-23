"""Certificates for the standard Borromean closed braid.

Keep this file beside check_colorings.py and jones_states.py.
"""

from math import gcd

from check_colorings import closed_count
from jones_states import jones


WORD = (1, -2) * 3


def inspect_strands():
    lanes = [1, 2, 3]
    crossings = []
    for letter in WORD:
        left = abs(letter) - 1
        a, b = lanes[left:left + 2]
        crossings.append((a, b, 1 if letter > 0 else -1))
        lanes[left:left + 2] = [b, a]
    assert lanes == [1, 2, 3]
    for delete in (1, 2, 3):
        retained = [sign for a, b, sign in crossings if delete not in (a, b)]
        assert sorted(retained) == [-1, 1]


def main():
    inspect_strands()
    for q in range(2, 16):
        assert closed_count(3, WORD, q) == q * gcd(q, 4) ** 2
    polynomial = jones(3, WORD)
    assert polynomial == {12: -1, 8: 3, 4: -2, 0: 4, -4: -2, -8: 3, -12: -1}
    assert max(polynomial) - min(polynomial) == 24
    assert sum(v * (-1 if (e // 4) % 2 else 1) for e, v in polynomial.items()) == 16
    print("Borromean checks passed: three deletions, 14 Fox counts, Jones coefficients and span.")


if __name__ == "__main__":
    main()
