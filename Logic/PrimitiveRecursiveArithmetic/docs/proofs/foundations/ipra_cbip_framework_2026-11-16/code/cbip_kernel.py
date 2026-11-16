"""Exact reference algorithms for Certified Bounded Interaction Programs.

This module is semantic regression evidence.  It is not an iPRA proof checker.
All arithmetic examples use Python integers or fractions.Fraction.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from typing import Any, Callable, Iterable, Mapping, Sequence


BoolPred = Callable[[int], bool]
Env = tuple[int, ...]


def all_below(bound: int, pred: BoolPred) -> bool:
    """Finite universal Boolean fold, true on the empty domain."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return all(pred(i) for i in range(bound))


def any_below(bound: int, pred: BoolPred) -> bool:
    """Finite existential Boolean fold, false on the empty domain."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return any(pred(i) for i in range(bound))


def first_success(bound: int, pred: BoolPred) -> int:
    """Least successful index, or the sentinel ``bound`` if none succeeds."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    for i in range(bound):
        if pred(i):
            return i
    return bound


# ---------------------------------------------------------------------------
# Fixed bounded formulas and two-sided certificates
# ---------------------------------------------------------------------------


class Formula:
    pass


@dataclass(frozen=True)
class Atom(Formula):
    test: Callable[[Env], bool]
    name: str = "atom"


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Exists(Formula):
    bound: Callable[[Env], int]
    body: Formula
    name: str = "exists"


@dataclass(frozen=True)
class Forall(Formula):
    bound: Callable[[Env], int]
    body: Formula
    name: str = "forall"


def formula_value(formula: Formula, env: Env = ()) -> bool:
    if isinstance(formula, Atom):
        return bool(formula.test(env))
    if isinstance(formula, And):
        return formula_value(formula.left, env) and formula_value(formula.right, env)
    if isinstance(formula, Or):
        return formula_value(formula.left, env) or formula_value(formula.right, env)
    if isinstance(formula, Exists):
        b = formula.bound(env)
        if b < 0:
            raise ValueError("formula bound must be nonnegative")
        return any(formula_value(formula.body, (i,) + env) for i in range(b))
    if isinstance(formula, Forall):
        b = formula.bound(env)
        if b < 0:
            raise ValueError("formula bound must be nonnegative")
        return all(formula_value(formula.body, (i,) + env) for i in range(b))
    raise TypeError(f"unsupported formula: {type(formula)!r}")


def canonical_certificate(formula: Formula, env: Env = ()) -> dict[str, Any]:
    """Build the canonical success or failure strategy certificate."""
    winner = formula_value(formula, env)

    if isinstance(formula, Atom):
        return {"tag": "atom", "winner": winner, "name": formula.name}

    if isinstance(formula, And):
        if winner:
            return {
                "tag": "and_all",
                "winner": True,
                "children": [
                    canonical_certificate(formula.left, env),
                    canonical_certificate(formula.right, env),
                ],
            }
        values = [formula_value(formula.left, env), formula_value(formula.right, env)]
        i = first_success(2, lambda j: not values[j])
        child = formula.left if i == 0 else formula.right
        return {
            "tag": "and_counterexample",
            "winner": False,
            "index": i,
            "child": canonical_certificate(child, env),
        }

    if isinstance(formula, Or):
        if winner:
            values = [formula_value(formula.left, env), formula_value(formula.right, env)]
            i = first_success(2, lambda j: values[j])
            child = formula.left if i == 0 else formula.right
            return {
                "tag": "or_choice",
                "winner": True,
                "index": i,
                "child": canonical_certificate(child, env),
            }
        return {
            "tag": "or_all_fail",
            "winner": False,
            "children": [
                canonical_certificate(formula.left, env),
                canonical_certificate(formula.right, env),
            ],
        }

    if isinstance(formula, Exists):
        b = formula.bound(env)
        if winner:
            i = first_success(b, lambda j: formula_value(formula.body, (j,) + env))
            assert i < b
            return {
                "tag": "exists_choice",
                "winner": True,
                "index": i,
                "child": canonical_certificate(formula.body, (i,) + env),
            }
        return {
            "tag": "exists_all_fail",
            "winner": False,
            "children": [
                canonical_certificate(formula.body, (i,) + env) for i in range(b)
            ],
        }

    if isinstance(formula, Forall):
        b = formula.bound(env)
        if winner:
            return {
                "tag": "forall_all",
                "winner": True,
                "children": [
                    canonical_certificate(formula.body, (i,) + env) for i in range(b)
                ],
            }
        i = first_success(b, lambda j: not formula_value(formula.body, (j,) + env))
        assert i < b
        return {
            "tag": "forall_counterexample",
            "winner": False,
            "index": i,
            "child": canonical_certificate(formula.body, (i,) + env),
        }

    raise TypeError(f"unsupported formula: {type(formula)!r}")


def check_certificate(
    formula: Formula, certificate: Mapping[str, Any], env: Env = ()
) -> bool:
    """Check a two-sided finite strategy certificate without trusting its winner."""
    try:
        tag = certificate["tag"]
        winner = certificate["winner"]
    except (KeyError, TypeError):
        return False
    if not isinstance(winner, bool):
        return False

    if isinstance(formula, Atom):
        return tag == "atom" and winner == bool(formula.test(env))

    if isinstance(formula, And):
        if winner:
            if tag != "and_all":
                return False
            children = certificate.get("children")
            return (
                isinstance(children, list)
                and len(children) == 2
                and check_certificate(formula.left, children[0], env)
                and children[0].get("winner") is True
                and check_certificate(formula.right, children[1], env)
                and children[1].get("winner") is True
            )
        if tag != "and_counterexample":
            return False
        i = certificate.get("index")
        if i not in (0, 1):
            return False
        child_formula = formula.left if i == 0 else formula.right
        child = certificate.get("child")
        return (
            isinstance(child, Mapping)
            and check_certificate(child_formula, child, env)
            and child.get("winner") is False
        )

    if isinstance(formula, Or):
        if winner:
            if tag != "or_choice":
                return False
            i = certificate.get("index")
            if i not in (0, 1):
                return False
            child_formula = formula.left if i == 0 else formula.right
            child = certificate.get("child")
            return (
                isinstance(child, Mapping)
                and check_certificate(child_formula, child, env)
                and child.get("winner") is True
            )
        if tag != "or_all_fail":
            return False
        children = certificate.get("children")
        return (
            isinstance(children, list)
            and len(children) == 2
            and check_certificate(formula.left, children[0], env)
            and children[0].get("winner") is False
            and check_certificate(formula.right, children[1], env)
            and children[1].get("winner") is False
        )

    if isinstance(formula, Exists):
        b = formula.bound(env)
        if winner:
            if tag != "exists_choice":
                return False
            i = certificate.get("index")
            child = certificate.get("child")
            return (
                isinstance(i, int)
                and 0 <= i < b
                and isinstance(child, Mapping)
                and check_certificate(formula.body, child, (i,) + env)
                and child.get("winner") is True
            )
        if tag != "exists_all_fail":
            return False
        children = certificate.get("children")
        return (
            isinstance(children, list)
            and len(children) == b
            and all(
                isinstance(child, Mapping)
                and check_certificate(formula.body, child, (i,) + env)
                and child.get("winner") is False
                for i, child in enumerate(children)
            )
        )

    if isinstance(formula, Forall):
        b = formula.bound(env)
        if winner:
            if tag != "forall_all":
                return False
            children = certificate.get("children")
            return (
                isinstance(children, list)
                and len(children) == b
                and all(
                    isinstance(child, Mapping)
                    and check_certificate(formula.body, child, (i,) + env)
                    and child.get("winner") is True
                    for i, child in enumerate(children)
                )
            )
        if tag != "forall_counterexample":
            return False
        i = certificate.get("index")
        child = certificate.get("child")
        return (
            isinstance(i, int)
            and 0 <= i < b
            and isinstance(child, Mapping)
            and check_certificate(formula.body, child, (i,) + env)
            and child.get("winner") is False
        )

    return False


# ---------------------------------------------------------------------------
# Deterministic bounded traces
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TraceSystem:
    good: Callable[[int], bool]
    init: Callable[[int], int]
    bound: Callable[[int], int]
    step: Callable[[int, int, int], int]
    invariant: Callable[[int, int, int], bool]
    accept: Callable[[int, int], bool]

    def states(self, u: int) -> list[int]:
        fuel = self.bound(u)
        if fuel < 0:
            raise ValueError("trace bound must be nonnegative")
        out = [self.init(u)]
        for i in range(fuel):
            out.append(self.step(i, out[-1], u))
        return out

    def check(self, u: int) -> bool:
        if not self.good(u):
            return True
        states = self.states(u)
        return all(self.invariant(i, s, u) for i, s in enumerate(states)) and self.accept(
            states[-1], u
        )


# ---------------------------------------------------------------------------
# Finite relational evidence
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class EvidenceMachine:
    start: Callable[[int], int]
    answer_bound: Callable[[int, int, int], int]
    halt: Callable[[int, int, int], bool]
    local: Callable[[int, int, int, int], bool]
    next_state: Callable[[int, int, int, int], int]
    post: Callable[[int, int, int], bool]

    def viability(self, x: int, horizon: int, state: int | None = None) -> bool:
        if horizon < 0:
            raise ValueError("horizon must be nonnegative")
        initial = self.start(x) if state is None else state

        @lru_cache(maxsize=None)
        def go(r: int, s: int) -> bool:
            if self.halt(x, r, s):
                return self.post(x, r, s)
            if r == 0:
                return False
            bound = self.answer_bound(x, r, s)
            if bound < 0:
                raise ValueError("answer bound must be nonnegative")
            return any(
                self.local(x, r, s, a)
                and go(r - 1, self.next_state(x, r, s, a))
                for a in range(bound)
            )

        return go(horizon, initial)

    def execute(self, x: int, horizon: int) -> tuple[list[int], int, int]:
        """Least-viable finite execution: transcript, terminal state, resource."""
        if horizon < 0:
            raise ValueError("horizon must be nonnegative")

        @lru_cache(maxsize=None)
        def go(r: int, s: int) -> bool:
            if self.halt(x, r, s):
                return self.post(x, r, s)
            if r == 0:
                return False
            return any(
                self.local(x, r, s, a)
                and go(r - 1, self.next_state(x, r, s, a))
                for a in range(self.answer_bound(x, r, s))
            )

        s = self.start(x)
        r = horizon
        if not go(r, s):
            raise ValueError("initial state is not viable")
        transcript: list[int] = []
        while not self.halt(x, r, s):
            if r == 0:
                raise AssertionError("viable zero-resource state must halt")
            b = self.answer_bound(x, r, s)
            a = first_success(
                b,
                lambda candidate: self.local(x, r, s, candidate)
                and go(r - 1, self.next_state(x, r, s, candidate)),
            )
            if a == b:
                raise AssertionError("viable state has no viable answer")
            transcript.append(a)
            s = self.next_state(x, r, s, a)
            r -= 1
        if not self.post(x, r, s):
            raise AssertionError("terminal viable state must satisfy postcondition")
        return transcript, s, r


# ---------------------------------------------------------------------------
# Exact quantitative helpers
# ---------------------------------------------------------------------------


def propagate_error(
    local_errors: Sequence[Fraction],
    dependencies: Sequence[Mapping[int, Fraction]],
) -> list[Fraction]:
    """Propagate a topologically ordered rational error DAG."""
    if len(local_errors) != len(dependencies):
        raise ValueError("local_errors and dependencies must have equal length")
    budgets: list[Fraction] = []
    for v, (eta, deps) in enumerate(zip(local_errors, dependencies)):
        total = eta
        for w, lipschitz in deps.items():
            if not (0 <= w < v):
                raise ValueError("dependencies must point to earlier nodes")
            if lipschitz < 0:
                raise ValueError("Lipschitz coefficients must be nonnegative")
            total += lipschitz * budgets[w]
        budgets.append(total)
    return budgets


def finite_argmin(values: Sequence[Fraction]) -> int:
    """Least index attaining the minimum; rejects an empty candidate list."""
    if not values:
        raise ValueError("argmin requires a nonempty finite list")
    best = 0
    for i in range(1, len(values)):
        if values[i] < values[best]:
            best = i
    return best


def dyadic_grid_argmin_residual(n: int) -> tuple[Fraction, Fraction]:
    """Least dyadic minimizer of |y^2-2| on [0,2]."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    den = 2**n
    grid = [Fraction(j, den) for j in range(2 * den + 1)]
    residuals = [abs(y * y - 2) for y in grid]
    i = finite_argmin(residuals)
    return grid[i], residuals[i]


def enumerate_integer_pairs(
    bound: int, predicate: Callable[[int, int], bool]
) -> list[tuple[int, int]]:
    """Canonical height-bounded enumeration in the square [-bound,bound]^2."""
    if bound < 0:
        raise ValueError("bound must be nonnegative")
    return [
        (x, y)
        for x in range(-bound, bound + 1)
        for y in range(-bound, bound + 1)
        if predicate(x, y)
    ]


def binary_halting_value(halting_time: int | None, n: int) -> int:
    if n < 0:
        raise ValueError("n must be nonnegative")
    return int(halting_time is not None and halting_time <= n)


def binary_metastable_window(
    halting_time: int | None, challenge: Callable[[int], int]
) -> int:
    """Finite-window selector from the barrier example.

    In a real machine instance, the finite simulation up to g(0) determines the
    same result.  ``halting_time`` is used here as exact test data.
    """
    g0 = challenge(0)
    if g0 < 0:
        raise ValueError("challenge values must be nonnegative")
    if halting_time is not None and halting_time <= g0:
        return halting_time
    return 0


def window_is_constant(
    halting_time: int | None, start: int, challenge: Callable[[int], int]
) -> bool:
    end = start + challenge(start)
    values = {binary_halting_value(halting_time, i) for i in range(start, end + 1)}
    return len(values) <= 1


__all__ = [
    "Atom",
    "And",
    "Or",
    "Exists",
    "Forall",
    "TraceSystem",
    "EvidenceMachine",
    "all_below",
    "any_below",
    "first_success",
    "formula_value",
    "canonical_certificate",
    "check_certificate",
    "propagate_error",
    "finite_argmin",
    "dyadic_grid_argmin_residual",
    "enumerate_integer_pairs",
    "binary_halting_value",
    "binary_metastable_window",
    "window_is_constant",
]
