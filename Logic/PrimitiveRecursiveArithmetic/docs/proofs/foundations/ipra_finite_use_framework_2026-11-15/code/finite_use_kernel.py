#!/usr/bin/env python3
"""Exact finite reference kernel for demand-driven relational certificates.

This module is executable evidence for finite instances only.  It is not an
iPRA proof checker and does not claim that arbitrary Python callables are
primitive recursive.  All numerical examples use integers and Fraction.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from typing import Callable, Generic, Hashable, Iterable, Optional, Sequence, TypeVar
import json

State = TypeVar("State", bound=Hashable)


def first_true(bound: int, predicate: Callable[[int], bool]) -> Optional[int]:
    """Return the least successful index below bound, or None."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    for i in range(bound):
        if predicate(i):
            return i
    return None


@dataclass(frozen=True)
class EvidenceMachine(Generic[State]):
    """A bounded adaptive relational consumer."""

    answer_bound: Callable[[int, State], int]
    halt: Callable[[int, State], bool]
    local: Callable[[int, State, int], bool]
    next_state: Callable[[int, State, int], State]
    post: Callable[[int, State], bool]


@dataclass(frozen=True)
class Transcript(Generic[State]):
    states: tuple[State, ...]
    answers: tuple[int, ...]

    @property
    def terminal(self) -> State:
        return self.states[-1]


def viability_solver(machine: EvidenceMachine[State]):
    """Return memoized viability and least-choice functions."""

    @lru_cache(maxsize=None)
    def viable(resource: int, state: State) -> bool:
        if resource < 0:
            return False
        if machine.halt(resource, state):
            return machine.post(resource, state)
        if resource == 0:
            return False
        bound = machine.answer_bound(resource, state)
        if bound < 0:
            raise ValueError("answer bound must be nonnegative")
        return any(
            machine.local(resource, state, answer)
            and viable(resource - 1, machine.next_state(resource, state, answer))
            for answer in range(bound)
        )

    def choose(resource: int, state: State) -> Optional[int]:
        if resource <= 0 or machine.halt(resource, state):
            return None
        return first_true(
            machine.answer_bound(resource, state),
            lambda answer: machine.local(resource, state, answer)
            and viable(resource - 1, machine.next_state(resource, state, answer)),
        )

    return viable, choose


def select_transcript(
    machine: EvidenceMachine[State], resource: int, start: State
) -> Transcript[State]:
    """Select the lexicographically least viable transcript."""
    viable, choose = viability_solver(machine)
    if not viable(resource, start):
        raise ValueError("initial state is not viable")

    states: list[State] = [start]
    answers: list[int] = []
    state = start
    remaining = resource

    while not machine.halt(remaining, state):
        if remaining == 0:
            raise AssertionError("viable nonterminal state at zero resource")
        answer = choose(remaining, state)
        if answer is None:
            raise AssertionError("viability did not yield an answer")
        if not machine.local(remaining, state, answer):
            raise AssertionError("selected answer is not locally valid")
        state = machine.next_state(remaining, state, answer)
        remaining -= 1
        answers.append(answer)
        states.append(state)

    if not machine.post(remaining, state):
        raise AssertionError("terminal postcondition failed")
    return Transcript(tuple(states), tuple(answers))


def check_transcript(
    machine: EvidenceMachine[State], resource: int, transcript: Transcript[State]
) -> bool:
    """Replay and verify a transcript independently of the selector."""
    if len(transcript.states) != len(transcript.answers) + 1:
        return False
    state = transcript.states[0]
    remaining = resource
    for answer, claimed_next in zip(transcript.answers, transcript.states[1:]):
        if remaining <= 0 or machine.halt(remaining, state):
            return False
        if answer < 0 or answer >= machine.answer_bound(remaining, state):
            return False
        if not machine.local(remaining, state, answer):
            return False
        actual_next = machine.next_state(remaining, state, answer)
        if actual_next != claimed_next:
            return False
        state = actual_next
        remaining -= 1
    return machine.halt(remaining, state) and machine.post(remaining, state)


def sqrt_candidates(a: Fraction, level: int) -> tuple[Fraction, ...]:
    """Finite dyadic candidates with a deliberately coarse residual gate."""
    if a < 0 or level < 0:
        raise ValueError("requires a >= 0 and level >= 0")
    scale = 1 << level
    # q <= a+2 is more than enough for the examples and is an explicit bound.
    upper = ((a.numerator + a.denominator - 1) // a.denominator + 2) * scale
    tolerance = Fraction(4, scale)
    return tuple(
        Fraction(j, scale)
        for j in range(upper + 1)
        if abs(Fraction(j * j, scale * scale) - a) <= tolerance
    )


def sqrt_chain_machine(a: Fraction, levels: int) -> tuple[EvidenceMachine[tuple[int, Optional[Fraction]]], tuple[tuple[Fraction, ...], ...]]:
    """Machine selecting a compatible candidate at each level."""
    if levels <= 0:
        raise ValueError("levels must be positive")
    candidates = tuple(sqrt_candidates(a, n) for n in range(levels))

    def answer_bound(_r: int, state: tuple[int, Optional[Fraction]]) -> int:
        level, _ = state
        return 0 if level >= levels else len(candidates[level])

    def halt(_r: int, state: tuple[int, Optional[Fraction]]) -> bool:
        return state[0] == levels

    def local(_r: int, state: tuple[int, Optional[Fraction]], answer: int) -> bool:
        level, previous = state
        if level >= levels or not (0 <= answer < len(candidates[level])):
            return False
        current = candidates[level][answer]
        if previous is None:
            return True
        # Edge from level-1 to level.
        return abs(current - previous) <= Fraction(2, 1 << (level - 1))

    def next_state(_r: int, state: tuple[int, Optional[Fraction]], answer: int) -> tuple[int, Optional[Fraction]]:
        level, _ = state
        return level + 1, candidates[level][answer]

    def post(_r: int, state: tuple[int, Optional[Fraction]]) -> bool:
        return state[0] == levels and state[1] is not None

    return EvidenceMachine(answer_bound, halt, local, next_state, post), candidates


def select_sqrt_chain(a: Fraction, levels: int) -> tuple[Fraction, ...]:
    machine, _ = sqrt_chain_machine(a, levels)
    transcript = select_transcript(machine, levels, (0, None))
    return tuple(state[1] for state in transcript.states[1:] if state[1] is not None)


@dataclass(frozen=True)
class ErrorNode:
    local_error: Fraction
    predecessors: tuple[tuple[int, Fraction], ...] = ()


def propagate_error_dag(nodes: Sequence[ErrorNode]) -> tuple[Fraction, ...]:
    """Compute E_v = eta_v + sum L_vw E_w in topological order."""
    budgets: list[Fraction] = []
    for index, node in enumerate(nodes):
        total = node.local_error
        if total < 0:
            raise ValueError("local errors must be nonnegative")
        for predecessor, multiplier in node.predecessors:
            if not (0 <= predecessor < index):
                raise ValueError("predecessors must be earlier nodes")
            if multiplier < 0:
                raise ValueError("multipliers must be nonnegative")
            total += multiplier * budgets[predecessor]
        budgets.append(total)
    return tuple(budgets)


def window_stable(
    sequence: Callable[[int], Fraction], start: int, width: int, epsilon: Fraction
) -> bool:
    if start < 0 or width < 0 or epsilon < 0:
        raise ValueError("invalid window arguments")
    values = [sequence(i) for i in range(start, start + width + 1)]
    return max(values) - min(values) <= epsilon


def find_metastable_window(
    sequence: Callable[[int], Fraction],
    challenge: Callable[[int], int],
    epsilon: Fraction,
    rank_bound: int,
) -> tuple[int, int]:
    """Search the standard iterated challenge candidates."""
    if epsilon <= 0 or rank_bound < 0:
        raise ValueError("epsilon must be positive and rank_bound nonnegative")
    start = 0
    for step in range(rank_bound + 1):
        width = challenge(start)
        if width < 0:
            raise ValueError("challenge must be nonnegative")
        if window_stable(sequence, start, width, epsilon):
            return start, step
        start = start + width + 1
    raise ValueError("no stable window found within supplied rank bound")


def enumerate_integer_points(
    bound: int, predicate: Callable[[int, int], bool]
) -> tuple[tuple[int, int], ...]:
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return tuple(
        (x, y)
        for x in range(-bound, bound + 1)
        for y in range(-bound, bound + 1)
        if predicate(x, y)
    )


def height_of_points(points: Iterable[tuple[int, int]]) -> int:
    maximum = 0
    for x, y in points:
        maximum = max(maximum, abs(x), abs(y))
    return maximum


def demo() -> dict[str, object]:
    chain = select_sqrt_chain(Fraction(2), 8)
    nodes = (
        ErrorNode(Fraction(1, 1024)),
        ErrorNode(Fraction(1, 2048), ((0, Fraction(3, 2)),)),
        ErrorNode(Fraction(1, 4096), ((0, Fraction(1, 3)), (1, Fraction(2)))),
    )
    budgets = propagate_error_dag(nodes)

    sequence = lambda n: Fraction(n, n + 8)
    challenge = lambda n: 3 + (n % 2)
    start, step = find_metastable_window(
        sequence, challenge, Fraction(1, 16), rank_bound=32
    )

    points = enumerate_integer_points(3, lambda x, y: x * x + y * y == 5)
    return {
        "sqrt2_chain": [str(q) for q in chain],
        "sqrt2_final_residual": str(abs(chain[-1] * chain[-1] - 2)),
        "error_budgets": [str(q) for q in budgets],
        "metastable_window": {
            "start": start,
            "challenge": challenge(start),
            "found_at_iteration": step,
        },
        "x2_plus_y2_eq_5": [list(point) for point in points],
        "point_height": height_of_points(points),
    }


def main() -> None:
    print(json.dumps(demo(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
