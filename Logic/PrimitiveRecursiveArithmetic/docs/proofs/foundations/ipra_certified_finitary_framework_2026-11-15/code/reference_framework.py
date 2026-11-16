"""Exact finite reference implementation for the iPRA framework.

This module is deliberately small and uses only Python's standard library.
It is a regression model for the finite algorithms described in the report;
it is not a substitute for object-language `Prf PRAAx` derivations.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Generic, Iterable, Sequence, TypeVar

T = TypeVar("T")


def all_fold(values: Iterable[bool]) -> bool:
    """Finite Boolean universal fold."""
    acc = True
    for value in values:
        acc = acc and bool(value)
    return acc


def any_fold(values: Iterable[bool]) -> bool:
    """Finite Boolean existential fold."""
    acc = False
    for value in values:
        acc = acc or bool(value)
    return acc


def least_true(bound: int, predicate: Callable[[int], bool]) -> int:
    """Least witness below ``bound``; sentinel ``bound`` when none exists."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    for index in range(bound):
        if predicate(index):
            return index
    return bound


def backward_schedule(
    demand: Callable[[int, int], int], terminal_time: int, terminal_query: int
) -> list[int]:
    """Return h[0..N], where h[N]=k and h[t]=D(t,h[t+1])."""
    if terminal_time < 0 or terminal_query < 0:
        raise ValueError("times and queries must be nonnegative")
    schedule = [0] * (terminal_time + 1)
    schedule[terminal_time] = terminal_query
    for time in range(terminal_time - 1, -1, -1):
        next_query = demand(time, schedule[time + 1])
        if next_query < 0:
            raise ValueError("demand returned a negative query")
        schedule[time] = next_query
    return schedule


def demand_transfer_check(
    property_at: Callable[[int, int], bool],
    demand: Callable[[int, int], int],
    terminal_time: int,
    terminal_query: int,
) -> bool:
    """Check the finite demand-transfer implication on concrete data.

    The function returns False if the base or a local implication fails.  When
    they all hold, it returns the final property value (which must then be True).
    """
    schedule = backward_schedule(demand, terminal_time, terminal_query)
    if not property_at(0, schedule[0]):
        return False
    for time in range(terminal_time):
        predecessor = demand(time, schedule[time + 1])
        if predecessor != schedule[time]:
            return False
        if property_at(time, predecessor) and not property_at(
            time + 1, schedule[time + 1]
        ):
            return False
    return property_at(terminal_time, terminal_query)


def prefix_max(values: Sequence[int]) -> int:
    """Maximum of a finite prefix, with empty maximum zero."""
    result = 0
    for value in values:
        if value < 0:
            raise ValueError("prefix_max expects nonnegative values")
        result = max(result, value)
    return result


def finite_query_envelope(
    count: Callable[[int, int], int],
    query: Callable[[int, int, int], int],
    stage: int,
    output_prefix: int,
) -> int:
    """Maximum predecessor query needed for outputs 0..output_prefix."""
    maxima: list[int] = []
    for output in range(output_prefix + 1):
        c = count(stage, output)
        maxima.append(prefix_max([query(stage, output, r) for r in range(c)]))
    return prefix_max(maxima)


@dataclass(frozen=True)
class LayeredRelation:
    """Finite layered relation over natural-number candidate codes."""

    bound: Callable[[int, int], int]  # (parameter, level) -> exclusive bound
    good: Callable[[int, int, int], bool]  # (parameter, level, candidate)
    compat: Callable[[int, int, int, int], bool]  # (p, level, a, b)

    def candidates(self, parameter: int, level: int) -> range:
        bound = self.bound(parameter, level)
        if bound < 0:
            raise ValueError("candidate bound must be nonnegative")
        return range(bound)

    def good_candidates(self, parameter: int, level: int) -> set[int]:
        return {
            candidate
            for candidate in self.candidates(parameter, level)
            if self.good(parameter, level, candidate)
        }


def backward_viability(
    relation: LayeredRelation, parameter: int, horizon: int
) -> list[set[int]]:
    """Viable candidates at every level for one fixed terminal horizon."""
    if horizon < 0:
        raise ValueError("horizon must be nonnegative")
    viable: list[set[int]] = [set() for _ in range(horizon + 1)]
    viable[horizon] = relation.good_candidates(parameter, horizon)
    for level in range(horizon - 1, -1, -1):
        next_viable = viable[level + 1]
        viable[level] = {
            candidate
            for candidate in relation.good_candidates(parameter, level)
            if any(
                relation.compat(parameter, level, candidate, successor)
                for successor in next_viable
            )
        }
    return viable


def forward_reachability(
    relation: LayeredRelation, parameter: int, horizon: int
) -> list[set[int]]:
    """Good candidates reachable from some good level-zero candidate."""
    if horizon < 0:
        raise ValueError("horizon must be nonnegative")
    reach: list[set[int]] = [set() for _ in range(horizon + 1)]
    reach[0] = relation.good_candidates(parameter, 0)
    for level in range(horizon):
        reach[level + 1] = {
            successor
            for successor in relation.good_candidates(parameter, level + 1)
            if any(
                relation.compat(parameter, level, candidate, successor)
                for candidate in reach[level]
            )
        }
    return reach


def full_viable_clouds(
    relation: LayeredRelation, parameter: int, horizon: int
) -> list[set[int]]:
    """Candidates lying on a complete path from level 0 to ``horizon``."""
    viable = backward_viability(relation, parameter, horizon)
    reach = forward_reachability(relation, parameter, horizon)
    return [reach[level] & viable[level] for level in range(horizon + 1)]


def least_viable_path(
    relation: LayeredRelation, parameter: int, horizon: int
) -> list[int]:
    """Lexicographically least complete viable path."""
    viable = backward_viability(relation, parameter, horizon)
    if not viable[0]:
        raise ValueError("no complete path exists")
    path = [min(viable[0])]
    for level in range(horizon):
        successors = [
            successor
            for successor in viable[level + 1]
            if relation.compat(parameter, level, path[-1], successor)
        ]
        if not successors:
            raise AssertionError("viability recurrence lost its successor")
        path.append(min(successors))
    return path


def path_ok(
    relation: LayeredRelation, parameter: int, path: Sequence[int]
) -> bool:
    """Check goodness/range/compatibility for a coded finite path."""
    if not path:
        return False
    for level, candidate in enumerate(path):
        if candidate not in relation.candidates(parameter, level):
            return False
        if not relation.good(parameter, level, candidate):
            return False
        if level + 1 < len(path) and not relation.compat(
            parameter, level, candidate, path[level + 1]
        ):
            return False
    return True


def least_valid_candidate(
    bound: int, valid: Callable[[int], bool]
) -> int:
    """Least valid candidate, raising when the finite cloud is empty."""
    candidate = least_true(bound, valid)
    if candidate == bound:
        raise ValueError("empty candidate cloud")
    return candidate


def stable_observable_selection(
    bound: Callable[[int], int],
    valid: Callable[[int, int], bool],
    observe: Callable[[int, int], T],
    precisions: Iterable[int],
) -> dict[int, T]:
    """Choose least certificates independently and expose only observations."""
    result: dict[int, T] = {}
    for precision in precisions:
        candidate = least_valid_candidate(
            bound(precision), lambda a, n=precision: valid(n, a)
        )
        result[precision] = observe(precision, candidate)
    return result


def verify_pairwise_stability(
    bound: Callable[[int], int],
    valid: Callable[[int, int], bool],
    observe: Callable[[int, int], T],
    distance: Callable[[T, T], Fraction],
    error: Callable[[int, int], Fraction],
    precisions: Sequence[int],
) -> bool:
    """Exhaustively check the finite pairwise certificate-stability contract."""
    for n in precisions:
        for m in precisions:
            for a in range(bound(n)):
                if not valid(n, a):
                    continue
                for b in range(bound(m)):
                    if not valid(m, b):
                        continue
                    if distance(observe(n, a), observe(m, b)) > error(n, m):
                        return False
    return True


def full_cloud_at(
    relation: LayeredRelation,
    parameter: int,
    level: int,
    horizon: int,
) -> set[int]:
    if horizon < level:
        raise ValueError("horizon must be at least the requested level")
    return full_viable_clouds(relation, parameter, horizon)[level]


def shrinking_selectors(
    relation: LayeredRelation,
    parameter: int,
    levels: Sequence[int],
    horizon: Callable[[int], int],
    observe: Callable[[int, int], Fraction],
) -> dict[int, Fraction]:
    """Least full-viable observations for changing finite horizons."""
    selected: dict[int, Fraction] = {}
    for level in levels:
        cloud = full_cloud_at(relation, parameter, level, horizon(level))
        if not cloud:
            raise ValueError(f"empty full-viable cloud at level {level}")
        selected[level] = observe(level, min(cloud))
    return selected


def verify_shrinking_bound(
    selected: dict[int, Fraction],
    epsilon: Callable[[int], Fraction],
    delta: Callable[[int], Fraction],
) -> bool:
    """Check |x_k-x_l| <= eps(k)+sum_{j=k}^{l-1}delta(j)."""
    levels = sorted(selected)
    for i, k in enumerate(levels):
        for ell in levels[i:]:
            tail = sum((delta(j) for j in range(k, ell)), Fraction(0))
            if abs(selected[k] - selected[ell]) > epsilon(k) + tail:
                return False
    return True


def finite_consumer_window_ok(
    sequence: Callable[[int], Fraction],
    base: int,
    control: Callable[[int], int],
    queries: Sequence[int],
    tolerance: Fraction,
) -> bool:
    """Verify that finite consumer queries lie in one stable window."""
    upper = base + control(base)
    if any(query < base or query > upper for query in queries):
        return False
    return all_fold(
        abs(sequence(i) - sequence(j)) <= tolerance
        for i in queries
        for j in queries
    )


def enumerate_with_height_bound(
    code_bound: Callable[[int], int],
    predicate: Callable[[int], bool],
    height: Callable[[int], int],
    height_bound: int,
) -> list[int]:
    """Exhaustive duplicate-free enumeration below a certified height bound."""
    if height_bound < 0:
        raise ValueError("height bound must be nonnegative")
    result: list[int] = []
    seen: set[int] = set()
    for code in range(code_bound(height_bound)):
        if predicate(code) and height(code) <= height_bound and code not in seen:
            seen.add(code)
            result.append(code)
    return result


def height_bound_from_complete_list(
    complete_list: Sequence[int], height: Callable[[int], int]
) -> int:
    """Finite maximum height, with empty maximum zero."""
    return prefix_max([height(code) for code in complete_list])
