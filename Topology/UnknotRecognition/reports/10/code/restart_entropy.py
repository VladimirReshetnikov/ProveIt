"""Exact sparse-lexicographic restart potentials, independent of topology.

A trace audit validates only the supplied finite trace. It does NOT prove that
an unspecified hierarchy algorithm always satisfies the sparsity hypothesis.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from functools import lru_cache
from math import comb
from typing import Iterable, Sequence


def _parameters(length: int, cap: int, support: int) -> None:
    if any(type(x) is not int or x < 0 for x in (length, cap, support)):
        raise ValueError("length, cap and support must be nonnegative integers")


@lru_cache(maxsize=4096)
def state_count(length: int, cap: int, support: int) -> int:
    """Number of length-L vectors in {0,...,g} with at most s nonzeros."""
    _parameters(length, cap, support)
    return sum(comb(length, j) * cap**j for j in range(min(length, support) + 1))


def lex_rank(vector: Sequence[int], cap: int, support: int) -> int:
    """Zero-based increasing lexicographic rank within the sparse state space."""
    length = len(vector)
    _parameters(length, cap, support)
    if any(type(x) is not int or x < 0 or x > cap for x in vector):
        raise ValueError("coordinate outside the declared range")
    if sum(x != 0 for x in vector) > support:
        raise ValueError("support exceeds the declared budget")
    rank, remaining = 0, support
    for i, x in enumerate(vector):
        if not x:
            continue
        tail = length - i - 1
        rank += state_count(tail, cap, remaining)  # smaller digit zero
        rank += (x - 1) * state_count(tail, cap, remaining - 1)
        remaining -= 1
    return rank


def lex_unrank(rank: int, length: int, cap: int, support: int) -> tuple[int, ...]:
    """Inverse rank; constructs the sharp countdown examples in the article."""
    _parameters(length, cap, support)
    if type(rank) is not int or not 0 <= rank < state_count(length, cap, support):
        raise ValueError("rank outside the state space")
    answer = []
    remaining = support
    for i in range(length):
        tail = length - i - 1
        zero_block = state_count(tail, cap, remaining)
        if rank < zero_block:
            answer.append(0)
        else:
            if remaining == 0 or cap == 0:
                raise ArithmeticError("invalid rank decomposition")
            rank -= zero_block
            positive_block = state_count(tail, cap, remaining - 1)
            digit, rank = divmod(rank, positive_block)
            answer.append(digit + 1)
            remaining -= 1
    return tuple(answer)


def audit_trace(trace: Iterable[Sequence[int]], cap: int, support: int) -> dict:
    """Validate strict lex descent and report a finite-trace potential bound."""
    previous = None
    length = None
    count = 0
    first = None
    last = None
    for vector in trace:
        if length is None:
            length = len(vector)
        elif len(vector) != length:
            raise ValueError("trace vectors must have a fixed padded length")
        rank = lex_rank(vector, cap, support)
        if previous is not None and rank >= previous:
            raise ValueError(f"trace fails strict descent at state {count}")
        if first is None:
            first = rank
        previous = last = rank
        count += 1
    if length is None:
        raise ValueError("empty trace")
    return {"length": length, "cap": cap, "support": support,
            "state_space": state_count(length, cap, support),
            "observed_states": count, "initial_rank": first, "final_rank": last,
            "states_bound_from_start": first + 1,
            "scope": "finite trace only; no topological hypotheses verified"}
