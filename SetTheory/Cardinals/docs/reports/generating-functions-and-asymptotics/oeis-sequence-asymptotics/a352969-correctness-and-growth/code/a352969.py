"""Exact enumeration and certified constructive bounds for OEIS A352969.

Python 3.9+; standard library only.  This is a new implementation of the
set recurrence, not a verbatim copy of the OEIS program.
"""
from __future__ import annotations

from functools import lru_cache
from itertools import combinations_with_replacement
from math import isqrt
from typing import FrozenSet, Iterable, Optional, Set


class PairBudgetExceeded(RuntimeError):
    """A requested stage exceeds an explicitly supplied pair budget."""


def _nonnegative_int(n: int, name: str = "n") -> None:
    if isinstance(n, bool) or not isinstance(n, int):
        raise TypeError(f"{name} must be an integer, not {type(n).__name__}")
    if n < 0:
        raise ValueError(f"{name} must be nonnegative")


def next_set(values: Iterable[int], *, pair_budget: Optional[int] = None) -> Set[int]:
    """One simultaneous step. The input is never mutated.

    The optional budget counts unordered input pairs, including equal pairs.
    Values must be positive Python integers. Deduplication of the input is
    intentional: the mathematical input is a set, not a multiset.
    """
    if pair_budget is not None:
        _nonnegative_int(pair_budget, "pair_budget")
    items = tuple(values)
    if not items:
        raise ValueError("the input set must not be empty")
    if any(isinstance(x, bool) or not isinstance(x, int) or x < 1
           for x in items):
        raise ValueError("all values must be positive Python integers")
    previous = frozenset(items)
    pairs = len(previous) * (len(previous) + 1) // 2
    if pair_budget is not None and pairs > pair_budget:
        raise PairBudgetExceeded(f"stage needs {pairs:,} pairs; budget is {pair_budget:,}")
    result: Set[int] = set()
    for x, y in combinations_with_replacement(previous, 2):
        result.add(x + y)
        result.add(x * y)
    return result


def reachable(n: int, *, pair_budget: Optional[int] = None) -> FrozenSet[int]:
    """Return S_n without retaining earlier stages in a global cache."""
    _nonnegative_int(n)
    if pair_budget is not None:
        _nonnegative_int(pair_budget, "pair_budget")
    current: Iterable[int] = {1}
    for _ in range(n):
        current = next_set(current, pair_budget=pair_budget)
    return frozenset(current)


@lru_cache(maxsize=None)
def _reachable_cached(n: int) -> FrozenSet[int]:
    if n == 0:
        return frozenset((1,))
    previous = _reachable_cached(n - 1)
    return frozenset(next_set(previous))


def reachable_cached(n: int) -> FrozenSet[int]:
    """Memoized variant. Immutable results prevent cache poisoning.

    Validation deliberately takes place outside the cached function.
    """
    _nonnegative_int(n)
    return _reachable_cached(n)


def clear_cache() -> None:
    _reachable_cached.cache_clear()


def a352969(n: int, *, pair_budget: Optional[int] = None) -> int:
    return len(reachable(n, pair_budget=pair_budget))


def maximum(n: int) -> int:
    """Exact maximum, M_0=1 and M_n=2**(2**(n-1)) for n>=1."""
    _nonnegative_int(n)
    return 1 if n == 0 else 1 << (1 << (n - 1))


def ceil_log2(n: int) -> int:
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError("ceil_log2 requires a positive integer")
    return (n - 1).bit_length()


def triangular_index(t: int) -> int:
    """Smallest r>=0 with t <= r*(r+1)//2, using exact integer arithmetic."""
    _nonnegative_int(t, "t")
    r = (isqrt(8 * t + 1) - 1) // 2
    if r * (r + 1) // 2 < t:
        r += 1
    return r


def uniform_depth_bound(t: int) -> int:
    """Every integer 1 <= m < 2**(2**t) has depth at most this bound."""
    _nonnegative_int(t, "t")
    return 0 if t == 0 else t + triangular_index(t) + 2


def counting_bound_parameters(n: int) -> dict:
    """Finite lower-bound certificate, n>=16; no enormous integers allocated.

    With e=lower_double_log2, the article proves a(n) >= 2**(2**e).
    """
    _nonnegative_int(n)
    if n < 16:
        raise ValueError("the stated uniform counting bound requires n >= 16")
    t = ceil_log2(2 * n)
    r = triangular_index(t)
    k = t + r + 2
    assert k <= n
    return {"n": n, "t": t, "r": r, "k": k,
            "log2_number_of_prime_factors": n - k,
            "lower_double_log2": n - r - 4,
            "upper_double_log2": n - 1}


def minimum_depths(limit: int) -> list[int]:
    """Independent value-indexed dynamic program for h(1),...,h(limit).

    It minimizes over all proper sum and product decompositions, rather
    than enumerating pairs of reachable values. O(limit**2) worst-case work.
    h[0] is an unused sentinel. Unit multiplications cannot improve a depth.
    """
    _nonnegative_int(limit, "limit")
    h = [0] * (limit + 1)
    for value in range(2, limit + 1):
        best = 1 + h[value - 1]
        for x in range(1, value // 2 + 1):
            candidate = 1 + max(h[x], h[value - x])
            if candidate < best:
                best = candidate
        for x in range(2, isqrt(value) + 1):
            if value % x == 0:
                candidate = 1 + max(h[x], h[value // x])
                if candidate < best:
                    best = candidate
        h[value] = best
    return h


class ExpressionBuilder:
    """Construct a +,* expression from 1, stored as an acyclic node table.

    A DAG is only a compact serialization: unfolding it produces a legal
    formula of exactly the same height. Cached integer values are used for
    verification, never as uncharged leaves in the expression.
    """
    def __init__(self) -> None:
        self.nodes = [{"op": "one"}]
        self.values = [1]
        self.heights = [0]
        self._intern: dict[tuple, int] = {}
        self._integers: dict[int, int] = {1: 0}
        self._powers: dict[int, int] = {0: 0}

    def _binary(self, op: str, left: int, right: int) -> int:
        if op not in ("add", "mul"):
            raise ValueError("unknown operation")
        # Both operations commute; canonical operand order shares nodes.
        left, right = sorted((left, right))
        key = (op, left, right)
        if key in self._intern:
            return self._intern[key]
        index = len(self.nodes)
        self.nodes.append({"op": op, "left": left, "right": right})
        a, b = self.values[left], self.values[right]
        self.values.append(a + b if op == "add" else a * b)
        self.heights.append(1 + max(self.heights[left], self.heights[right]))
        self._intern[key] = index
        return index

    def power_of_two(self, exponent: int) -> int:
        _nonnegative_int(exponent, "exponent")
        if exponent in self._powers:
            return self._powers[exponent]
        if exponent == 1:
            root = self._binary("add", 0, 0)
        else:
            half = exponent // 2
            root = self._binary("mul", self.power_of_two(half),
                                self.power_of_two(exponent - half))
        self._powers[exponent] = root
        return root

    def _balanced_sum(self, terms: list[int]) -> int:
        if not terms:
            raise ValueError("zero is not a legal formula value")
        while len(terms) > 1:
            following = [self._binary("add", terms[i], terms[i + 1])
                         for i in range(0, len(terms) - 1, 2)]
            if len(terms) % 2:
                following.append(terms[-1])
            terms = following
        return terms[0]

    def integer(self, value: int) -> int:
        if isinstance(value, bool) or not isinstance(value, int) or value < 1:
            raise ValueError("value must be a positive integer")
        if value in self._integers:
            return self._integers[value]
        t = ceil_log2(value.bit_length())
        r = triangular_index(t)
        width = 1 << (t - r)
        mask = (1 << width) - 1
        rest, index = value, 0
        terms = []
        while rest:
            digit = rest & mask
            if digit:
                digit_root = self.integer(digit)
                if index == 0:
                    term = digit_root
                elif digit == 1:
                    term = self.power_of_two(index * width)
                else:
                    term = self._binary("mul", digit_root,
                                        self.power_of_two(index * width))
                terms.append(term)
            rest >>= width
            index += 1
        root = self._balanced_sum(terms)
        assert self.values[root] == value
        assert self.heights[root] <= uniform_depth_bound(t)
        self._integers[value] = root
        return root

    def certificate(self, root: int) -> dict:
        return {"format": "positive-integer-formula-dag-v1", "root": root,
                "value_hex": hex(self.values[root]),
                "height": self.heights[root], "nodes": self.nodes}


def check_certificate(certificate: dict) -> tuple[int, int]:
    """Independently evaluate a serialized formula DAG and check its height."""
    values, heights = [], []
    for i, node in enumerate(certificate["nodes"]):
        op = node.get("op")
        if op == "one":
            values.append(1)
            heights.append(0)
            continue
        if op not in ("add", "mul"):
            raise ValueError(f"bad opcode at node {i}")
        left, right = node["left"], node["right"]
        if (type(left) is not int or type(right) is not int
                or not (0 <= left < i and 0 <= right < i)):
            raise ValueError(f"non-acyclic operand reference at node {i}")
        values.append(values[left] + values[right] if op == "add"
                      else values[left] * values[right])
        heights.append(1 + max(heights[left], heights[right]))
    root = certificate["root"]
    if type(root) is not int or not (0 <= root < len(values)):
        raise ValueError("invalid root")
    if values[root] != int(certificate["value_hex"], 16):
        raise ValueError("value mismatch")
    if heights[root] != certificate["height"]:
        raise ValueError("height mismatch")
    return values[root], heights[root]
