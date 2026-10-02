"""Signed closure correlations, computed without enumerating matchings.

F(lambda) = sum_Q (-1)^(c(M,Q)+c(N,Q)), where the alternating cycle
half-lengths of M union N form lambda.  The recurrence is proved in the paper.
"""
from __future__ import annotations
from functools import lru_cache
from fractions import Fraction
from typing import Iterator


def partitions(n: int, maximum: int | None = None) -> Iterator[tuple[int, ...]]:
    if n == 0:
        yield ()
        return
    for k in range(min(n, n if maximum is None else maximum), 0, -1):
        for tail in partitions(n - k, k):
            yield (k,) + tail


def matching_count(n: int) -> int:
    v = 1
    for k in range(1, n + 1):
        v *= 2 * k - 1
    return v


def canonical(parts) -> tuple[int, ...]:
    return tuple(sorted(parts, reverse=True))


@lru_cache(None)
def signed_sum(parts: tuple[int, ...]) -> int:
    if not parts:
        return 1
    n = sum(parts)
    if 1 in parts:
        q = list(parts)
        q.remove(1)
        return (2 * n - 1) * signed_sum(tuple(q))
    k, mu = parts[0], parts[1:]
    ans = (k - 3) * signed_sum(canonical((k - 1,) + mu))
    for i in range(1, k - 1):
        ans += signed_sum(canonical((i, k - 1 - i) + mu))
    for j, ell in enumerate(mu):
        other = mu[:j] + mu[j + 1:]
        ans += 2 * ell * signed_sum(canonical((k + ell - 1,) + other))
    return ans


def correlation(parts: tuple[int, ...]) -> Fraction:
    return Fraction(signed_sum(canonical(parts)), matching_count(sum(parts)))


def representative(parts: tuple[int, ...]):
    m, n, offset = [], [], 0
    for k in parts:
        for j in range(k):
            m.append((offset + 2*j, offset + 2*j + 1))
            n.append(tuple(sorted((offset + 2*j + 1, offset + 2*((j+1) % k)))))
        offset += 2*k
    return tuple(sorted(m)), tuple(sorted(n))
