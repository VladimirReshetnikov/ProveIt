"""Finite names below epsilon_omega, with named fixed points of omega power.

A word is a tuple of atoms in nonincreasing order. Marker(i) contributes
epsilon_i; Power(exponent) contributes omega**exponent. The canonical
representation of omega**epsilon_i is the same marker singleton.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import product


@dataclass(frozen=True)
class Marker:
    index: int


@dataclass(frozen=True)
class Power:
    exponent: Word


Word = tuple[Marker | Power, ...]


def epsilon(i: int) -> Word:
    if type(i) is not int or i < 0:
        raise ValueError("the marker index must be a natural number")
    return (Marker(i),)


def is_marker(word: Word) -> bool:
    return len(word) == 1 and isinstance(word[0], Marker)


@lru_cache(None)
def level(word: Word) -> int:
    return max((atom.index + 1 if isinstance(atom, Marker) else level(atom.exponent)
                for atom in word), default=0)


@lru_cache(None)
def order_key(word: Word) -> tuple:
    """Lexicographic implementation of the mutually recursive atom/word order."""
    return tuple((atom.index + 1, 0, ()) if isinstance(atom, Marker)
                 else (level(atom.exponent), 1, order_key(atom.exponent))
                 for atom in word)


def valid(word: Word) -> bool:
    if not isinstance(word, tuple):
        return False
    for atom in word:
        if isinstance(atom, Marker):
            if type(atom.index) is not int or atom.index < 0:
                return False
        elif isinstance(atom, Power):
            if not valid(atom.exponent) or is_marker(atom.exponent):
                return False
        else:
            return False
    keys = order_key(word)
    return all(first >= second for first, second in zip(keys, keys[1:]))


def compare(u: Word, v: Word) -> int:
    ku, kv = order_key(u), order_key(v)
    return (ku > kv) - (ku < kv)


def omega_power(u: Word) -> Word:
    return u if is_marker(u) else (Power(u),)


def successor(u: Word) -> Word:
    return u + (Power(()),)


@lru_cache(None)
def depth(u: Word) -> int:
    if not u:
        return 0
    return 1 + max((depth(atom.exponent) for atom in u if isinstance(atom, Power)),
                   default=0)


def tower(i: int, steps: int) -> Word:
    if min(i, steps) < 0:
        raise ValueError("tower indices must be nonnegative")
    value = successor(epsilon(i - 1)) if i else successor(())
    for _ in range(steps):
        value = omega_power(value)
    return value


def _old_value(word: Word, gap: int) -> tuple:
    """Finite comparison check only: replace markers by widely spaced towers.

    Old CNFs are nested tuples of exponents without markers. This independent
    evaluation is used on the depth-bounded sample below. It is not a map
    preserving the marker fixed-point equations.
    """
    def exponent_of_marker(i):
        value = ()
        for _ in range((i + 1) * gap - 1):
            value = (value,)
        return value

    return tuple(exponent_of_marker(atom.index) if isinstance(atom, Marker)
                 else _old_value(atom.exponent, gap) for atom in word)


def selfcheck():
    zero = ()
    one = successor(zero)
    two = successor(one)
    omega = omega_power(one)
    sample = {zero, one, two, omega, successor(omega), omega_power(two)}
    for i in range(3):
        e = epsilon(i)
        assert valid(e) and not valid((Power(e),))
        assert not valid((Power(zero), Marker(i)))
        sample.update((e, e + e, successor(e), successor(e + e)))
        sample.update(tower(i, j) for j in range(5))
    sample.update(omega_power(u) for u in tuple(sample))
    sample.update(successor(u) for u in tuple(sample))
    # Exercise lists with various levels, including markers in a trailing term.
    for u in tuple(sample):
        for i in range(3):
            if u and compare(u[-1:], epsilon(i)) >= 0:
                sample.add(u + epsilon(i))
    assert all(valid(u) for u in sample)
    gap = max(map(depth, sample)) + 3
    evaluated = {u: _old_value(u, gap) for u in sample}
    for u in sample:
        wu = omega_power(u)
        assert valid(wu) and level(u) == level(wu)
        assert (compare(u, wu) == 0) == is_marker(u) and compare(u, wu) <= 0
        assert compare(u, epsilon(level(u))) < 0
        for i in range(4):
            if compare(u, epsilon(i)) < 0:
                bigger = tower(i, depth(u))
                assert compare(u, bigger) < 0 and compare(bigger, epsilon(i)) < 0
    for u, v in product(sample, repeat=2):
        cmp = compare(u, v)
        ou, ov = evaluated[u], evaluated[v]
        assert cmp == (ou > ov) - (ou < ov)
        assert (cmp == 0) == (u == v)
        assert cmp == compare(omega_power(u), omega_power(v))
    print(f"Checked {len(sample)} epsilon words, their cofinal witnesses, "
          f"and {len(sample)**2} ordered pairs.")


if __name__ == "__main__":
    selfcheck()
