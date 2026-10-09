"""Exact classical left-greedy braid normal forms, with checkable move traces.

Permutation convention: p[i] is the bottom position of top strand i (zero based).
No permutation quotient or hash fingerprint is used as a braid equality test.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Iterable

Permutation = tuple[int, ...]
State = tuple[int, tuple[Permutation, ...]]
IDENTITY: State = (0, ())

@dataclass
class Counters:
    appends: int = 0
    transfers: int = 0
    pair_tests: int = 0
    peak_factors: int = 0
    prefix_height: int = 0

class LimitExceeded(RuntimeError):
    """A cooperative operation allowance was exhausted; no decision follows."""

@dataclass
class Budget:
    max_ticks: int | None = None
    ticks: int = 0
    hook: Callable[[], None] | None = None
    def __post_init__(self) -> None:
        if self.max_ticks is not None and (type(self.max_ticks) is not int or self.max_ticks < 0):
            raise ValueError("max_ticks must be a nonnegative integer or None")
        if type(self.ticks) is not int or self.ticks < 0:
            raise ValueError("ticks must be a nonnegative integer")
        if self.hook is not None and not callable(self.hook):
            raise ValueError("hook must be callable or None")
    def check(self) -> None:
        if self.hook is not None:
            self.hook()
        self.ticks += 1
        if self.max_ticks is not None and self.ticks > self.max_ticks:
            raise LimitExceeded("normal-form/DP operation allowance exhausted")


def validate(b: int, word: Iterable[int]) -> tuple[int, ...]:
    if type(b) is not int or b < 1:
        raise ValueError("strand count must be a positive integer")
    ans = tuple(word)
    if any(type(a) is not int or a == 0 or abs(a) >= b for a in ans):
        raise ValueError("letters must be nonzero integers with absolute value < strands")
    return ans


def _inverse(p: Permutation) -> list[int]:
    inv = [0] * len(p)
    for i, v in enumerate(p):
        inv[v] = i
    return inv


def _swap_values(p: Permutation, i: int) -> Permutation:
    return tuple(i + 1 if x == i else i if x == i + 1 else x for x in p)


def _swap_positions(p: Permutation, i: int) -> Permutation:
    q = list(p)
    q[i], q[i + 1] = q[i + 1], q[i]
    return tuple(q)


def append(state: State, letter: int, b: int, *,
           trace: bool = False, counters: Counters | None = None,
           budget: Budget | None = None) -> tuple[State, dict | None]:
    """Right multiply a valid normal form by one signed Artin generator.

    The optional trace contains only local simple-braid atom transfers and a
    count of leading half-twists removed; it can be replayed without this code.
    This is an internal operation: callers validate input words at entry.
    """
    if budget:
        budget.check()
    power, old = state
    factors = list(old)
    unit = tuple(range(b))
    delta = tuple(reversed(unit))
    i = abs(letter) - 1
    if letter > 0:
        factors.append(_swap_positions(unit, i))
    else:
        power -= 1
        factors = [tuple(b - 1 - x for x in reversed(p)) for p in factors]
        complement = _swap_values(delta, i)  # Delta sigma_i^{-1}
        if complement != unit:
            factors.append(complement)
    if counters:
        counters.appends += 1
        counters.peak_factors = max(counters.peak_factors, len(factors))
    moves = [] if trace else None
    j = 0
    while j + 1 < len(factors):
        if budget:
            budget.check()
        if counters:
            counters.pair_tests += 1
        left, right = factors[j], factors[j + 1]
        inv = _inverse(left)
        movable = next((i for i in range(b - 1)
                        if right[i] > right[i + 1] and inv[i] < inv[i + 1]), None)
        if movable is None:
            j += 1
            continue
        factors[j] = _swap_values(left, movable)
        factors[j + 1] = _swap_positions(right, movable)
        if trace:
            moves.append([j, movable + 1])
        if counters:
            counters.transfers += 1
        if factors[j + 1] == unit:
            del factors[j + 1]
        j = max(0, j - 1)
    extracted = 0
    while factors and factors[0] == delta:
        del factors[0]
        power += 1
        extracted += 1
    result = (power, tuple(factors))
    proof = {"moves": moves, "delta": extracted} if trace else None
    return result, proof


def normal_form(b: int, word: Iterable[int], *, trace: bool = False,
                counters: Counters | None = None,
                budget: Budget | None = None) -> tuple[State, list[dict] | None]:
    if budget:
        budget.check()
    word = validate(b, word)
    state = IDENTITY
    proof = [] if trace else None
    for letter in word:
        state, step = append(state, letter, b, trace=trace, counters=counters,
                             budget=budget)
        if trace:
            proof.append(step)
    if budget:
        budget.check()
    return state, proof


def is_normal(b: int, state: State) -> bool:
    p, factors = state
    unit = tuple(range(b))
    delta = tuple(reversed(unit))
    if type(p) is not int or any(tuple(sorted(f)) != unit for f in factors):
        return False
    if any(f == unit or f == delta for f in factors):
        return False
    for left, right in zip(factors, factors[1:]):
        inv = _inverse(left)
        if any(right[i] > right[i + 1] and inv[i] < inv[i + 1]
               for i in range(b - 1)):
            return False
    return True


def simple_word(p: Permutation) -> tuple[int, ...]:
    """A reduced positive word of the unique simple braid with permutation p."""
    q = list(p)
    prefix = []
    while q != sorted(q):
        i = next(i for i in range(len(q) - 1) if q[i] > q[i + 1])
        prefix.append(i + 1)
        q[i], q[i + 1] = q[i + 1], q[i]
    return tuple(prefix)


def expand_state(b: int, state: State) -> tuple[int, ...]:
    """Polynomial-length representative, intended for small independent tests."""
    p, factors = state
    delta = tuple(i for k in range(b - 1, 0, -1) for i in range(1, k + 1))
    root = delta if p >= 0 else tuple(-a for a in reversed(delta))
    return root * abs(p) + tuple(a for f in factors for a in simple_word(f))
