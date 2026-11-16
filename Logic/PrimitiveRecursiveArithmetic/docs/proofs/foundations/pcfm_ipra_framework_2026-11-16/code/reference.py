"""Executable reference models for the PCFM paper.

These algorithms use Python integers and fractions only.  They are regression
evidence for finite constructions, not object-iPRA proofs.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable, Sequence, TypeAlias


# ---------------------------------------------------------------------------
# Quantifier-free Boolean reflection (semantic reference)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Eq:
    left: Callable[[tuple[int, ...]], int]
    right: Callable[[tuple[int, ...]], int]


@dataclass(frozen=True)
class Bot:
    pass


@dataclass(frozen=True)
class And:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Or:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Imp:
    left: "Formula"
    right: "Formula"


Formula: TypeAlias = Eq | Bot | And | Or | Imp


def eval_formula(phi: Formula, env: tuple[int, ...]) -> bool:
    """Classical finite semantics used only to regression-test the compiler."""
    if isinstance(phi, Eq):
        return phi.left(env) == phi.right(env)
    if isinstance(phi, Bot):
        return False
    if isinstance(phi, And):
        return eval_formula(phi.left, env) and eval_formula(phi.right, env)
    if isinstance(phi, Or):
        return eval_formula(phi.left, env) or eval_formula(phi.right, env)
    if isinstance(phi, Imp):
        return (not eval_formula(phi.left, env)) or eval_formula(phi.right, env)
    raise TypeError(f"unknown formula: {phi!r}")


def bnot(b: int) -> int:
    _require_bit(b)
    return 1 - b


def band(b: int, c: int) -> int:
    _require_bit(b)
    _require_bit(c)
    return b * c


def bor(b: int, c: int) -> int:
    _require_bit(b)
    _require_bit(c)
    return 1 - (1 - b) * (1 - c)


def bimp(b: int, c: int) -> int:
    return bor(bnot(b), c)


def _require_bit(b: int) -> None:
    if b not in (0, 1):
        raise ValueError(f"expected Boolean bit, got {b}")


def compile_qf(phi: Formula) -> Callable[[tuple[int, ...]], int]:
    """Return the characteristic bit of a fixed QF formula."""
    if isinstance(phi, Eq):
        return lambda env: int(phi.left(env) == phi.right(env))
    if isinstance(phi, Bot):
        return lambda env: 0
    if isinstance(phi, And):
        l = compile_qf(phi.left)
        r = compile_qf(phi.right)
        return lambda env: band(l(env), r(env))
    if isinstance(phi, Or):
        l = compile_qf(phi.left)
        r = compile_qf(phi.right)
        return lambda env: bor(l(env), r(env))
    if isinstance(phi, Imp):
        l = compile_qf(phi.left)
        r = compile_qf(phi.right)
        return lambda env: bimp(l(env), r(env))
    raise TypeError(f"unknown formula: {phi!r}")


def bounded_all(n: int, pred_bit: Callable[[int], int]) -> int:
    if n < 0:
        raise ValueError("bound must be nonnegative")
    acc = 1
    for i in range(n):
        bit = pred_bit(i)
        _require_bit(bit)
        acc = band(acc, bit)
    return acc


def bounded_least(n: int, pred_bit: Callable[[int], int]) -> int:
    """Least i < n with pred_bit(i)=1, or n if no witness exists."""
    if n < 0:
        raise ValueError("bound must be nonnegative")
    for i in range(n):
        bit = pred_bit(i)
        _require_bit(bit)
        if bit == 1:
            return i
    return n


# ---------------------------------------------------------------------------
# Fixed traces
# ---------------------------------------------------------------------------

State: TypeAlias = tuple[int, ...]


def run_trace(
    initial: State,
    step: Callable[[int, State], State],
    clock: int,
) -> list[State]:
    if clock < 0:
        raise ValueError("clock must be nonnegative")
    states = [initial]
    state = initial
    for t in range(clock):
        state = step(t, state)
        states.append(state)
    return states


def check_invariant(
    trace: Sequence[State],
    invariant: Callable[[int, State], bool],
) -> bool:
    return all(invariant(t, state) for t, state in enumerate(trace))


# ---------------------------------------------------------------------------
# Backward viability
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ViabilityResult:
    viable: tuple[tuple[bool, ...], ...]
    next_choice: tuple[tuple[int | None, ...], ...]


def backward_viability(
    bounds: Sequence[int],
    good: Callable[[int, int], bool],
    compatible: Callable[[int, int, int], bool],
    terminal: Callable[[int], bool],
) -> ViabilityResult:
    """Compute viability for levels 0..T.

    `bounds[t]` is the number of candidates at level t.
    `compatible(t, a, b)` relates levels t and t+1.
    """
    if not bounds or any(b < 0 for b in bounds):
        raise ValueError("bounds must be a nonempty sequence of nonnegative integers")

    horizon = len(bounds) - 1
    viable: list[list[bool]] = [[False] * b for b in bounds]
    choice: list[list[int | None]] = [[None] * b for b in bounds]

    for a in range(bounds[horizon]):
        viable[horizon][a] = good(horizon, a) and terminal(a)

    for t in range(horizon - 1, -1, -1):
        for a in range(bounds[t]):
            if not good(t, a):
                continue
            for b in range(bounds[t + 1]):
                if compatible(t, a, b) and viable[t + 1][b]:
                    viable[t][a] = True
                    choice[t][a] = b
                    break

    return ViabilityResult(
        tuple(tuple(row) for row in viable),
        tuple(tuple(row) for row in choice),
    )


def select_viable_path(result: ViabilityResult) -> tuple[int, ...] | None:
    """Select the least viable initial node and stored least successors."""
    initial = next((a for a, ok in enumerate(result.viable[0]) if ok), None)
    if initial is None:
        return None
    path = [initial]
    a = initial
    for t in range(len(result.viable) - 1):
        b = result.next_choice[t][a]
        if b is None:
            raise AssertionError("viability table lacks a successor choice")
        path.append(b)
        a = b
    return tuple(path)


def exact_stable_observation(
    witnesses: Iterable[int],
    observation: Callable[[int], int],
) -> int:
    """Return the least witness's observation after checking exact stability."""
    ws = sorted(set(witnesses))
    if not ws:
        raise ValueError("witness set must be nonempty")
    values = {observation(w) for w in ws}
    if len(values) != 1:
        raise ValueError("observer is not stable on the witness set")
    return observation(ws[0])


# ---------------------------------------------------------------------------
# Exact rational bisection for y^3 + y = q
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo

    @property
    def midpoint(self) -> Fraction:
        return (self.lo + self.hi) / 2


def cubic_value(y: Fraction, q: Fraction) -> Fraction:
    return y * y * y + y - q


def cubic_bisect(q: Fraction, interval: Interval, steps: int) -> list[Interval]:
    if steps < 0:
        raise ValueError("steps must be nonnegative")
    if not interval.lo < interval.hi:
        raise ValueError("interval must have positive width")
    if cubic_value(interval.lo, q) > 0 or cubic_value(interval.hi, q) < 0:
        raise ValueError("interval does not bracket a root")

    trace = [interval]
    current = interval
    for _ in range(steps):
        mid = current.midpoint
        if cubic_value(mid, q) <= 0:
            current = Interval(mid, current.hi)
        else:
            current = Interval(current.lo, mid)
        trace.append(current)
    return trace


def check_cubic_trace(q: Fraction, trace: Sequence[Interval]) -> bool:
    if not trace:
        return False
    initial_width = trace[0].width
    for t, interval in enumerate(trace):
        if not interval.lo < interval.hi:
            return False
        if cubic_value(interval.lo, q) > 0:
            return False
        if cubic_value(interval.hi, q) < 0:
            return False
        if interval.width * (2**t) != initial_width:
            return False
    return True


# ---------------------------------------------------------------------------
# Bounded enumeration
# ---------------------------------------------------------------------------

def complete_bounded_list(
    candidates: Sequence[int],
    valid: Callable[[int], bool],
    equation: Callable[[int], bool],
    equivalent: Callable[[int, int], bool],
) -> tuple[int, ...]:
    """Scan candidates and keep one representative of each valid solution."""
    out: list[int] = []
    for x in candidates:
        if not valid(x) or not equation(x):
            continue
        if not any(equivalent(x, y) for y in out):
            out.append(x)
    return tuple(out)
