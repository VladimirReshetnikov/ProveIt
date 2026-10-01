"""Exact algorithms for Sharp Isolation Thresholds for Binary Insertion.

Python >= 3.10, standard library only.  All calculations use integers.
The fast classifier applies to m >= 3.  Exhaustive algorithms are deliberately
independent of its scalar test; they are practical only on finite small inputs.
"""
from __future__ import annotations
from itertools import combinations
from math import comb
from typing import Iterator, Sequence

Vector = tuple[int, ...]


def checked_vector(v: Sequence[int], m: int) -> Vector:
    if not isinstance(m, int) or m < 1:
        raise ValueError("m must be a positive integer")
    v = tuple(v)
    if not v or any(not isinstance(x, int) or x < 0 for x in v):
        raise ValueError("v must be a nonempty vector of nonnegative integers")
    return v


def compositions(n: int, g: int) -> Iterator[Vector]:
    """Generate all weak compositions; no large persistent cache is retained."""
    if n < 0 or g < 0:
        return
    if g == 0:
        if n == 0:
            yield ()
    elif g == 1:
        yield (n,)
    else:
        for x in range(n + 1):
            for rest in compositions(n - x, g - 1):
                yield (x,) + rest


def partitions(n: int, g: int, lower: int = 0) -> Iterator[Vector]:
    """Generate nondecreasing vectors, one per coordinate-permutation orbit."""
    if g == 0:
        if n == 0:
            yield ()
    elif g == 1:
        if n >= lower:
            yield (n,)
    else:
        for x in range(lower, n // g + 1):
            for rest in partitions(n - x, g - 1, x):
                yield (x,) + rest


def feasible(v: Sequence[int], m: int) -> bool:
    """The proved O(g)-arithmetic-operation center criterion (m >= 3)."""
    v = checked_vector(v, m)
    if m < 3:
        raise ValueError("the center classification requires m >= 3")
    if sum(x > 0 for x in v) < m or sum(v) <= len(v) * (m - 1):
        return False
    h = tuple(max(0, x - m + 1) for x in v)
    H, M = sum(h), max(h)
    if H - M > m:
        return True
    if H - M != m:
        return False
    j = h.index(M)
    return all(x <= 1 for i, x in enumerate(h) if i != j)


def admissible(beta: Vector, v: Vector, m: int) -> bool:
    """Membership in the maximal target language preserving center degree m."""
    if len(beta) != len(v) or sum(beta) != sum(v) - m:
        return False
    if any(b < 0 for b in beta):
        return False
    if any(b > x for b, x in zip(beta, v)):
        return True
    return all(x - b in (0, 1) for b, x in zip(beta, v))


def maximal_targets(v: Sequence[int], m: int) -> Iterator[Vector]:
    v = checked_vector(v, m)
    for beta in compositions(sum(v) - m, len(v)):
        if admissible(beta, v, m):
            yield beta


def literal_word(v: Sequence[int]) -> str:
    return "b".join("a" * x for x in v)


def gap_vector(word: str) -> Vector:
    if any(c not in "ab" for c in word):
        raise ValueError("word must be binary")
    return tuple(len(run) for run in word.split("b"))


def full_output_test(v: Sequence[int], m: int) -> tuple[bool, Vector | None, int]:
    """Direct one-piece coverage test for E_max, not using feasible().

    Return (success, first uncovered noncenter, number of outputs inspected).
    Degree m at the center is checked by the existence of a binary deficit.
    """
    v = checked_vector(v, m)
    if sum(x > 0 for x in v) < m:
        return False, v, 0
    count = 0
    for c in compositions(sum(v), len(v)):
        count += 1
        if c == v:
            continue
        for j, x in enumerate(c):
            if x >= m:
                beta = c[:j] + (x - m,) + c[j + 1:]
                if admissible(beta, v, m):
                    break
        else:
            return False, c, count
    return True, None, count


def deletion_test(v: Sequence[int], m: int) -> tuple[bool, Vector | None, int]:
    """Enumerate every forbidden deficit and its unique-predecessor neighbors.

    This is independent of the h/H/M criterion, but uses the proved volume
    obstruction. Return the first counterexample when a local one is found.
    """
    v = checked_vector(v, m)
    if m < 3:
        raise ValueError("the deficit/volume test requires m >= 3")
    if sum(x > 0 for x in v) < m or sum(v) <= len(v) * (m - 1):
        return False, None, 0
    count = 0
    for delta in compositions(m, len(v)):
        count += 1
        if any(d > x for d, x in zip(delta, v)) or max(delta) <= 1:
            continue
        beta = tuple(x - d for x, d in zip(v, delta))
        for j in range(len(v)):
            c = beta[:j] + (beta[j] + m,) + beta[j + 1:]
            if c != v and all(c[i] < m for i in range(len(v)) if i != j):
                return False, c, count
    return True, None, count


def threshold(m: int) -> int:
    if m < 3:
        raise ValueError("the threshold theorem requires m >= 3")
    return 12 if m == 3 else 5 * m - 2


def minimum_total(m: int, g: int) -> int:
    if g < m:
        raise ValueError("no isolated degree-m center exists when g < m")
    return max(g * (m - 1) + 1, threshold(m))


def canonical_center(m: int, g: int, T: int | None = None) -> Vector:
    """Produce a feasible center for every feasible triple (m,g,T), m >= 3."""
    bound = minimum_total(m, g)
    if T is None:
        T = bound
    if T < bound:
        raise ValueError("the requested parameter triple is not feasible")
    base = [4, 4, 4] if m == 3 else [2 * m, 2 * m] + [1] * (m - 2)
    base += [0] * (g - m)
    base[0] += T - sum(base)
    return tuple(base)


def minimum_length(m: int) -> int:
    if m < 2:
        raise ValueError("m must be >= 2")
    return 3 if m == 2 else minimum_total(m, m) + m - 1


def bounded_positive(total: int, parts: int, cap: int) -> int:
    """Number of positive compositions with a common upper bound."""
    if parts == 0:
        return int(total == 0)
    if total < parts or cap < 1 or total > parts * cap:
        return 0
    return sum((-1) ** j * comb(parts, j) * comb(total - j * cap - 1, parts - 1)
               for j in range(min(parts, (total - parts) // cap) + 1))


def extremal_count(m: int) -> int:
    """Count distinct ordered gap vectors, not target languages or masks."""
    if m == 2:
        return 1
    T = minimum_total(m, m)
    result = 0
    for k in range(2, m + 1):
        for H in range(k, T + 1):
            low_total = T - k * (m - 1) - H
            result += (comb(m, k) * bounded_positive(H, k, H - m - 1)
                       * bounded_positive(low_total, m - k, m - 1))
    return result


def literal_singleton_degrees(m: int, target: str) -> tuple[dict[str, int], int]:
    """Enumerate position masks in actual words, independently of gap geometry."""
    if m < 1 or any(c not in "ab" for c in target):
        raise ValueError("positive m and a binary target are required")
    n = m + len(target)
    degrees: dict[str, int] = {}
    masks = 0
    for positions in combinations(range(n), m):
        masks += 1
        inserted = set(positions)
        it = iter(target)
        w = "".join("a" if i in inserted else next(it) for i in range(n))
        runs = sum(i == 0 or positions[i] != positions[i - 1] + 1 for i in range(m))
        degrees[w] = min(degrees.get(w, runs), runs)
    return degrees, masks


def predecessors(c: Vector, m: int) -> Iterator[Vector]:
    for j, x in enumerate(c):
        if x >= m:
            yield c[:j] + (x - m,) + c[j + 1:]


def mandatory_extremal_target(beta: Vector, v: Vector, m: int) -> bool:
    """Explicit mandatory-target theorem for a feasible center with g=m.

    A non-special admissible target is mandatory exactly when it has at most
    one coordinate >=m, or has two and one transfer produces a forbidden target.
    """
    if len(v) != m or not feasible(v, m):
        raise ValueError("a feasible center with g=m is required")
    if not admissible(beta, v, m):
        return False
    special = tuple(x - 1 for x in v)
    if beta == special:
        return True
    high = [i for i, x in enumerate(beta) if x >= m]
    if len(high) <= 1:
        return True
    if len(high) > 2:
        return False
    p, q = high
    for i, j in ((p, q), (q, p)):
        shifted = list(beta)
        shifted[i] += m
        shifted[j] -= m
        if not admissible(tuple(shifted), v, m):
            return True
    return False
