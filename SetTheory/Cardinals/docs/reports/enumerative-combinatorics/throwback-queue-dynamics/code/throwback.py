"""Exact throwback dynamics, static recurrence certificates, and period formulas.

Python 3.10+, standard library only. Tokens are labeled by original index;
repeated integer weights NEVER identify their tokens.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, lcm, prod
from typing import Iterable, Sequence


def positive_int(value: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError("Weights must be positive Python integers.")
    return value


@dataclass(frozen=True)
class Obstruction:
    """Finite, checkable description of the recurrent core of any extension."""
    first_bad_index: int
    threshold: int
    prefix: tuple[int, ...]
    core_labels: tuple[int, ...]

    @property
    def core_weights(self) -> tuple[int, ...]:
        return tuple(self.prefix[i] for i in self.core_labels)

    def verify(self) -> bool:
        """Independent sorted-prefix check; does not replay the parking algorithm."""
        j, m = self.first_bad_index, self.threshold
        if j != len(self.prefix) - 1 or m < 1:
            return False
        if any(x < 1 for x in self.prefix):
            return False
        old = sorted(self.prefix[:-1])
        if any(x < k + 1 for k, x in enumerate(old)):
            return False
        new = sorted(self.prefix)
        bad = next((k for k, x in enumerate(new) if x <= k), None)
        return (bad == m and
                self.core_labels == tuple(i for i, x in enumerate(self.prefix) if x <= m)
                and len(self.core_labels) == m + 1)


class OccupiedIntervals:
    """Union-by-size DSU of occupied integer slots, with interval minima.

    Each connected component consists of consecutive occupied slots. Sparse
    dictionaries avoid allocating up to the largest (possibly huge) weight.
    """
    def __init__(self) -> None:
        self.parent: dict[int, int] = {}
        self.size: dict[int, int] = {}
        self.minimum: dict[int, int] = {}

    def find(self, x: int) -> int:
        root = x
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[x] != x:
            nxt = self.parent[x]
            self.parent[x] = root
            x = nxt
        return root

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]
        self.minimum[a] = min(self.minimum[a], self.minimum[b])

    def predecessor_free(self, deadline: int) -> int:
        if deadline not in self.parent:
            return deadline
        return self.minimum[self.find(deadline)] - 1

    def occupy(self, slot: int) -> None:
        if slot <= 0 or slot in self.parent:
            raise ValueError("Slot must be a free positive integer.")
        self.parent[slot] = slot
        self.size[slot] = 1
        self.minimum[slot] = slot
        for neighbor in (slot - 1, slot + 1):
            if neighbor in self.parent:
                self.union(slot, neighbor)


def first_obstruction(weights: Iterable[int]) -> Obstruction | None:
    """Stop at the first overloaded prefix, using sparse backward parking.

    On a finite admissible input, None means ONLY that the inspected prefix
    has no obstruction. An infinite admissible input does not terminate.
    At failure, closure of parking-slot deadlines recovers the least
    overloaded threshold in linear additional time.
    """
    slots = OccupiedIntervals()
    occupant: dict[int, int] = {}
    prefix: list[int] = []
    for value in weights:
        value = positive_int(value)
        j = len(prefix)
        slot = slots.predecessor_free(value)
        prefix.append(value)
        if slot == 0:
            threshold = value
            cursor = 1
            while cursor <= threshold:
                old_label = occupant[cursor]
                threshold = max(threshold, prefix[old_label])
                cursor += 1
            core = tuple(sorted([occupant[p] for p in range(1, threshold + 1)] + [j]))
            result = Obstruction(j, threshold, tuple(prefix), core)
            return result
        slots.occupy(slot)
        occupant[slot] = j
    return None


def admissible(weights: Sequence[int]) -> bool:
    values = sorted(positive_int(x) for x in weights)
    return all(x >= i + 1 for i, x in enumerate(values))


def critical(weights: Sequence[int]) -> bool:
    n = len(weights)
    if n < 2 or any(isinstance(x, bool) or not isinstance(x, int) or x < 1 for x in weights):
        return False
    values = sorted(weights)
    return values[-1] == n - 1 and all(x >= i + 1 for i, x in enumerate(values[:-1]))


def finite_orbit(weights: Sequence[int]) -> tuple[int, list[tuple[int, ...]], list[int]]:
    """Actual labeled finite queue, requiring every weight < queue length.

    Returns transient length, states before each move, and the leader labels.
    The returned list stops immediately before the first repeated state.
    """
    values = tuple(positive_int(x) for x in weights)
    n = len(values)
    if n < 2 or any(x >= n for x in values):
        raise ValueError("A finite queue must be closed: 1 <= weight < length.")
    state = tuple(range(n))
    seen: dict[tuple[int, ...], int] = {}
    states: list[tuple[int, ...]] = []
    leaders: list[int] = []
    while state not in seen:
        seen[state] = len(states)
        states.append(state)
        head, *tail = state
        leaders.append(head)
        tail.insert(values[head], head)
        state = tuple(tail)
    return seen[state], states, leaders


def sorted_statistics(weights: Sequence[int], *, closed: bool = False) -> dict:
    """Exact period, per-token densities, and bounded configuration count.

    In open mode the selected multiset must be admissible; remaining tokens
    have weight >= its maximum, and '*' is the unselected leader symbol.
    In closed mode the selected multiset must be critical.
    """
    s = tuple(sorted(positive_int(x) for x in weights))
    if closed:
        if not critical(s):
            raise ValueError("Closed statistics require a critical multiset.")
    elif not admissible(s):
        raise ValueError("Open statistics require an admissible selected multiset.")
    q = tuple(x - i + 1 for i, x in enumerate(s))
    remaining = Fraction(1)
    frequencies = []
    period_lcm = 1
    for stride in q:
        freq = remaining / stride
        frequencies.append(freq)
        period_lcm = lcm(period_lcm, freq.denominator)
        remaining -= freq
    p = 1
    steps = []
    for stride in reversed(q):
        divisor = gcd(p, stride - 1)
        p = stride * p // divisor
        steps.append((stride, divisor, p))
    assert p == period_lcm
    count = prod(q)
    pairwise = all(gcd(q[i] - 1, q[j]) == 1
                   for i in range(len(q)) for j in range(i + 1, len(q)))
    assert (p == count) == pairwise
    return dict(sorted_weights=s, strides=q, frequencies=tuple(frequencies),
                remaining=remaining, period=p, configurations=count,
                cycles=count // p, perfect_mixing=pairwise,
                backward_steps=tuple(reversed(steps)))


def bounded_step(weights: Sequence[int], state: tuple[int, ...]) -> tuple[int, ...]:
    """Autonomous positions of selected tokens; no zero means a '*' move."""
    if 0 not in state:
        return tuple(p - 1 for p in state)
    leader = state.index(0)
    distance = weights[leader]
    return tuple(distance if i == leader else p - (p <= distance)
                 for i, p in enumerate(state))


def bounded_inverse(weights: Sequence[int], state: tuple[int, ...]) -> tuple[int, ...]:
    matches = [i for i, p in enumerate(state) if p == weights[i]]
    if not matches:
        return tuple(p + 1 for p in state)
    leader = min(matches, key=lambda i: weights[i])
    distance = weights[leader]
    return tuple(0 if i == leader else p + (p < distance)
                 for i, p in enumerate(state))


def finite_horizon(weights: Sequence[int], steps: int, window: int = 1) -> tuple[list[int], tuple[int, ...]]:
    """Exact leaders and final visible prefix from sufficiently long input.

    Requires len(weights) >= steps + window. A throw beyond the represented
    prefix is discarded, NEVER incorrectly appended to the finite queue.
    An omitted token cannot return to the visible window within the horizon.
    """
    if steps < 0 or window < 1 or len(weights) < steps + window:
        raise ValueError("Need nonnegative steps and at least steps+window weights.")
    values = tuple(positive_int(x) for x in weights)
    queue = list(range(len(values)))
    leaders = []
    for _ in range(steps):
        head = queue.pop(0)
        leaders.append(head)
        distance = values[head]
        if distance <= len(queue):
            queue.insert(distance, head)
    return leaders, tuple(queue[:window])


def certified_orbit(certificate: Obstruction, max_steps: int = 1000000) -> dict:
    """Exact whole leader sequence from a finite obstruction, without its tail.

    Keeps only the positions of prefix tokens, even for astronomically large
    weights. The step cap is a resource limit, not a conjectured time bound.
    """
    if not certificate.verify() or max_steps < 1:
        raise ValueError("Need a valid obstruction and a positive step cap.")
    weights = certificate.prefix
    state = tuple(range(len(weights)))
    seen = {}
    states = []
    leaders = []
    while state not in seen:
        if len(states) >= max_steps:
            raise TimeoutError("Orbit exceeds max_steps; static certificate remains valid.")
        if 0 not in state:
            raise AssertionError("A tail token would lead, contradicting the certificate.")
        seen[state] = len(states)
        states.append(state)
        leader = state.index(0)
        leaders.append(leader)
        state = bounded_step(weights, state)
    transient = seen[state]
    period = len(states) - transient
    word = [weights[i] for i in leaders[transient:]]
    numeric_period = next(d for d in range(1, period + 1)
                          if period % d == 0 and
                          all(word[i] == word[i % d] for i in range(period)))
    return dict(transient=transient, labeled_period=period,
                numerical_period=numeric_period, leaders=leaders,
                numerical_leaders=[weights[i] for i in leaders],
                periodic_state=states[transient])


def maximum_core_period(r: int) -> tuple[int, int]:
    """Return (maximum labeled period, one maximizing K) for core size r."""
    if isinstance(r, bool) or not isinstance(r, int) or r < 2:
        raise ValueError("Core size must be an integer >= 2.")
    return max((k ** (r - k + 1), k) for k in range(2, r + 1))


if __name__ == "__main__":
    import json
    examples = [[2, 100, 2, 1, 1], [1, 2, 3, 1], [2, 2, 2, 1, 1], [1, 1, 2, 2, 2]]
    for example in examples:
        cert = first_obstruction(example)
        assert cert is not None and cert.verify()
        result = {"input": example, "first_bad_index": cert.first_bad_index,
                  "threshold": cert.threshold, "core_labels": cert.core_labels,
                  "core_weights": cert.core_weights,
                  "statistics": sorted_statistics(cert.core_weights, closed=True)}
        print(json.dumps(result, default=str))
