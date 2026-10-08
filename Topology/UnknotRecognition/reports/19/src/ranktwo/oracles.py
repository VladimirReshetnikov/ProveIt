"""Slow independent test oracles; not the production shortening path."""
from __future__ import annotations
from collections.abc import Iterable
from .common import validate_word
from .verify import local_equal


def brute_optimum(strands: int, word: Iterable[int], radius: int = 1) -> int:
    """Enumerate all intervals and permitted targets, return optimal saved length."""
    word = validate_word(strands, word)
    n = len(word)
    best = [0] * (n + 1)
    for stop in range(1, n + 1):
        best[stop] = best[stop - 1]
        for start in range(stop):
            source = word[start:stop]
            support = sorted({abs(g) for g in source})
            if len(support) > 2:
                continue
            targets = [0] if radius == 0 else [0] + [g for i in support for g in (i, -i)]
            for target in targets:
                gain = stop - start - int(target != 0)
                if gain > 0 and local_equal(source, target):
                    best[stop] = max(best[stop], best[start] + gain)
    return best[-1]


def free_reduce(word: Iterable[int]) -> tuple[int, ...]:
    stack: list[int] = []
    for x in word:
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
    return tuple(stack)


def inverse(word: Iterable[int]) -> tuple[int, ...]:
    return tuple(-g for g in reversed(tuple(word)))


def artin_action(strands: int, word: Iterable[int], *, max_letters: int = 1_000_000
                 ) -> tuple[tuple[int, ...], ...]:
    """Action on a free group: independent equality oracle for small tests.

    Expanded free-group words can grow exponentially. This function has an
    explicit resource guard and is never used in the complexity theorem.
    """
    word = validate_word(strands, word)
    images = [(i + 1,) for i in range(strands)]
    for g in word:
        j = abs(g) - 1
        a, b = images[j], images[j + 1]
        if g > 0:
            images[j], images[j + 1] = free_reduce(a + b + inverse(a)), a
        else:
            images[j], images[j + 1] = b, free_reduce(inverse(b) + a + b)
        if sum(map(len, images)) > max_letters:
            raise RuntimeError('expanded Artin-action oracle exceeded its resource guard')
    return tuple(images)


def burau_minus_one(word: Iterable[int]) -> tuple[tuple[int, int, int, int], int]:
    a, b, c, d, exponent = 1, 0, 0, 1, 0
    for g in word:
        exponent += 1 if g > 0 else -1
        if g == 1:
            b, d = a + b, c + d
        elif g == -1:
            b, d = b - a, d - c
        elif g == 2:
            a, c = a - b, c - d
        elif g == -2:
            a, c = a + b, c + d
        else:
            raise ValueError('Burau oracle requires B3 letters')
    return (a, b, c, d), exponent
