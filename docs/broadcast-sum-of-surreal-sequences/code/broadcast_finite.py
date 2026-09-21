"""Exact finite model of Lipparini's sign-truncation game.

This evaluates finite families of finite canonical sign strings.  It does NOT
approximate the infinite game by taking a limit; the accompanying paper proves
that such a limit would in general be wrong.  Python 3.10+, standard library only.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from itertools import product
from typing import Iterable

State = tuple[str, ...]


def validate_signs(s: str) -> None:
    if not isinstance(s, str) or any(c not in '+-' for c in s):
        raise ValueError('A sign string must contain only + and -.')


@lru_cache(maxsize=None)
def sign_value(s: str) -> Fraction:
    """The exact dyadic value of a finite canonical sign expansion."""
    validate_signs(s)
    if not s:
        return Fraction(0)
    first = s[0]
    k = 0
    while k < len(s) and s[k] == first:
        k += 1
    value = Fraction(k if first == '+' else -k)
    step = Fraction(1, 2)
    for c in s[k:]:
        value += step if c == '+' else -step
        step /= 2
    return value


def truncate(s: str, sign: str, threshold: int) -> str:
    """Cut immediately before the first requested sign at/after threshold."""
    validate_signs(s)
    if sign not in ('+', '-') or threshold < 0:
        raise ValueError('Invalid sign or negative threshold.')
    cut = s.find(sign, threshold)
    return s if cut == -1 else s[:cut]


def apply(state: State, sign: str, threshold: int,
          exempt: frozenset[int] = frozenset()) -> State:
    return tuple(s if i in exempt else truncate(s, sign, threshold)
                 for i, s in enumerate(state))


def legal(state: State, sign: str, threshold: int,
          exempt: frozenset[int] = frozenset()) -> bool:
    return any(i not in exempt and threshold < len(s) and s[threshold] == sign
               for i, s in enumerate(state))


def legal_actions(state: State, sign: str
                  ) -> Iterable[tuple[int, frozenset[int]]]:
    """All legal (threshold, finite-exemption-set) actions on this finite state."""
    for mask in range(1 << len(state)):
        exempt = frozenset(i for i in range(len(state)) if mask & (1 << i))
        thresholds = {j for i, s in enumerate(state) if i not in exempt
                      for j, c in enumerate(s) if c == sign}
        for threshold in sorted(thresholds):
            yield threshold, exempt


@lru_cache(maxsize=None)
def followers(state: State, sign: str) -> frozenset[State]:
    return frozenset(apply(state, sign, t, f) for t, f in legal_actions(state, sign))


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -floor_fraction(-x)


def simplest_between(left: Fraction | None, right: Fraction | None) -> Fraction:
    """The simplest dyadic strictly inside a nonempty dyadic interval.

    None represents an absent bound. Integer candidates are tried first in
    order of simplicity, then denominators 2, 4, 8, ... . This is exact.
    """
    if left is not None and right is not None and left >= right:
        raise ValueError('The numerical cut is not separated.')
    if (left is None or left < 0) and (right is None or 0 < right):
        return Fraction(0)
    if left is not None and left >= 0:
        candidate = Fraction(floor_fraction(left) + 1)
        if right is None or candidate < right:
            return candidate
    elif right is not None and right <= 0:
        candidate = Fraction(ceil_fraction(right) - 1)
        if left is None or left < candidate:
            return candidate
    assert left is not None and right is not None
    denominator = 2
    while True:
        first = floor_fraction(left * denominator) + 1
        last = ceil_fraction(right * denominator) - 1
        if first <= last:
            # At the first successful denominator there is only one candidate;
            # retaining a nearest-zero choice also makes the routine robust.
            numerator = min(max(0, first), last)
            return Fraction(numerator, denominator)
        denominator *= 2


@lru_cache(maxsize=None)
def game_value(state: State) -> Fraction:
    """Recursively build and evaluate the actual finite broadcast game tree."""
    for s in state:
        validate_signs(s)
    left = [game_value(t) for t in followers(state, '+')]
    right = [game_value(t) for t in followers(state, '-')]
    return simplest_between(max(left) if left else None,
                            min(right) if right else None)


def sign_strings(max_length: int) -> tuple[str, ...]:
    if max_length < 0:
        raise ValueError('max_length must be nonnegative')
    return tuple(''.join(signs) for n in range(max_length + 1)
                 for signs in product('+-', repeat=n))


def power_and_upgrade(n: int, d: int) -> tuple[str, str]:
    if n < 0 or d < 1:
        raise ValueError('Require n >= 0 and d >= 1.')
    base = '+' + '-' * (n + d)
    return base, base + '+'


if __name__ == '__main__':
    example = ('+--+', '+---+', '+----+')
    print('State:', example)
    print('Finite broadcast value:', game_value(example))
    print('Ordinary finite sum:', sum(map(sign_value, example), Fraction(0)))
    print('The infinite all-upgraded sequence is NOT evaluated by this program.')
