"""Exact finite reference algorithms for the FQNF iPRA framework.

This module is deliberately ordinary executable mathematics, not an iPRA proof
checker.  It exercises the finite algorithms whose object-theory correctness is
specified in the accompanying paper and Lean plan.

Only the Python standard library is used.  All analytic examples use
``fractions.Fraction``; no floating point arithmetic occurs.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import prod
from typing import Callable, Iterable, Sequence, TypeVar

T = TypeVar("T")
O = TypeVar("O")


def _require_nonnegative(name: str, value: int) -> None:
    if value < 0:
        raise ValueError(f"{name} must be nonnegative, got {value}")


def encode_digits(digits: Sequence[int], base: int) -> int:
    """Encode little-endian base-``base`` digits as one natural number.

    The least significant digit is ``digits[0]``.  The function validates the
    digit bounds, because those bounds are precisely the certificate side
    conditions used by the mathematical normalization theorem.
    """

    if base < 2:
        raise ValueError(f"base must be at least 2, got {base}")
    code = 0
    place = 1
    for index, value in enumerate(digits):
        if not 0 <= value < base:
            raise ValueError(
                f"digit {index} must lie in [0,{base}), got {value}"
            )
        code += value * place
        place *= base
    return code


def digit(code: int, index: int, base: int) -> int:
    """Return the ``index``-th little-endian digit of ``code`` in ``base``."""

    _require_nonnegative("code", code)
    _require_nonnegative("index", index)
    if base < 2:
        raise ValueError(f"base must be at least 2, got {base}")
    return (code // (base**index)) % base


def decode_digits(code: int, length: int, base: int) -> tuple[int, ...]:
    """Decode exactly ``length`` little-endian digits."""

    _require_nonnegative("code", code)
    _require_nonnegative("length", length)
    if base < 2:
        raise ValueError(f"base must be at least 2, got {base}")
    return tuple(digit(code, index, base) for index in range(length))


def encode_mixed_radix(values: Sequence[int], radices: Sequence[int]) -> int:
    """Encode a tuple whose component ``i`` is bounded by ``radices[i]``.

    This is the mixed-radix packing used for a master certificate.  Its global
    bound is ``prod(radices)``.
    """

    if len(values) != len(radices):
        raise ValueError("values and radices must have the same length")
    code = 0
    place = 1
    for index, (value, radix) in enumerate(zip(values, radices, strict=True)):
        if radix <= 0:
            raise ValueError(f"radix {index} must be positive, got {radix}")
        if not 0 <= value < radix:
            raise ValueError(
                f"component {index} must lie in [0,{radix}), got {value}"
            )
        code += place * value
        place *= radix
    return code


def decode_mixed_radix(code: int, radices: Sequence[int]) -> tuple[int, ...]:
    """Decode a mixed-radix tuple from a code below the product bound."""

    _require_nonnegative("code", code)
    if any(radix <= 0 for radix in radices):
        raise ValueError("all radices must be positive")
    bound = prod(radices)
    if code >= bound and bound != 0:
        raise ValueError(f"code {code} is outside the mixed-radix bound {bound}")
    values: list[int] = []
    quotient = code
    for radix in radices:
        values.append(quotient % radix)
        quotient //= radix
    return tuple(values)


def least_certificate(bound: int, valid: Callable[[int], bool]) -> int | None:
    """Return the least valid code below ``bound``, or ``None``.

    Object-iPRA uses the repository's primitive-recursive bounded search rather
    than this Python loop.  The observable behavior is intentionally the same.
    """

    _require_nonnegative("bound", bound)
    for code in range(bound):
        if valid(code):
            return code
    return None


@dataclass(frozen=True)
class FinitePathProblem:
    """A finite-horizon relational path problem.

    ``level_sizes[t]`` bounds the state at time ``t``.  The whole path is one
    certificate.  This allows a future-dependent path to be selected without
    assuming countable or dependent choice.
    """

    level_sizes: tuple[int, ...]
    start_ok: Callable[[int], bool]
    edge_ok: Callable[[int, int, int], bool]
    final_ok: Callable[[int], bool]

    def __post_init__(self) -> None:
        if not self.level_sizes:
            raise ValueError("a path problem must have at least one level")
        if any(size <= 0 for size in self.level_sizes):
            raise ValueError("every level must have a positive finite size")

    @property
    def base(self) -> int:
        return max(2, max(self.level_sizes))

    @property
    def code_bound(self) -> int:
        return self.base ** len(self.level_sizes)


def verify_path(problem: FinitePathProblem, path: Sequence[int]) -> bool:
    """Check the complete path certificate."""

    if len(path) != len(problem.level_sizes):
        return False
    if any(
        not 0 <= state < problem.level_sizes[time]
        for time, state in enumerate(path)
    ):
        return False
    if not problem.start_ok(path[0]):
        return False
    for time in range(len(path) - 1):
        if not problem.edge_ok(time, path[time], path[time + 1]):
            return False
    return problem.final_ok(path[-1])


def decode_path(problem: FinitePathProblem, code: int) -> tuple[int, ...]:
    """Decode a path code using a uniform base."""

    return decode_digits(code, len(problem.level_sizes), problem.base)


def find_path_by_whole_code(
    problem: FinitePathProblem,
) -> tuple[int, tuple[int, ...]] | None:
    """Search the bounded space of complete path certificates."""

    code = least_certificate(
        problem.code_bound,
        lambda candidate: verify_path(problem, decode_path(problem, candidate)),
    )
    if code is None:
        return None
    path = decode_path(problem, code)
    assert verify_path(problem, path)
    return code, path


def greedy_path(problem: FinitePathProblem) -> tuple[int, ...] | None:
    """Choose the least locally available state at each stage.

    This intentionally naive selector is useful as a counterexample: local
    least choice can get stuck even though a complete bounded path exists.
    """

    starts = [s for s in range(problem.level_sizes[0]) if problem.start_ok(s)]
    if not starts:
        return None
    path = [min(starts)]
    for time in range(len(problem.level_sizes) - 1):
        next_states = [
            nxt
            for nxt in range(problem.level_sizes[time + 1])
            if problem.edge_ok(time, path[-1], nxt)
        ]
        if not next_states:
            return None
        path.append(min(next_states))
    if not problem.final_ok(path[-1]):
        return None
    return tuple(path)


def complete_bounded_list(bound: int, valid: Callable[[int], bool]) -> tuple[int, ...]:
    """Enumerate every valid code below an explicit height/code bound."""

    _require_nonnegative("bound", bound)
    return tuple(code for code in range(bound) if valid(code))


def verify_complete_bounded_list(
    bound: int, valid: Callable[[int], bool], values: Iterable[int]
) -> bool:
    """Check that ``values`` is exactly the valid set below ``bound``."""

    expected = complete_bounded_list(bound, valid)
    received = tuple(values)
    return received == expected


@dataclass(frozen=True)
class IntervalCertificate:
    """A rational enclosure certificate for one real observation."""

    precision: int
    lower: Fraction
    upper: Fraction

    def __post_init__(self) -> None:
        _require_nonnegative("precision", self.precision)
        if self.lower > self.upper:
            raise ValueError("lower endpoint exceeds upper endpoint")

    @property
    def width(self) -> Fraction:
        return self.upper - self.lower

    @property
    def midpoint(self) -> Fraction:
        return (self.lower + self.upper) / 2


def interval_valid(cert: IntervalCertificate, target: Fraction) -> bool:
    """Reference validity predicate for a rational target."""

    return (
        cert.lower <= target <= cert.upper
        and cert.width <= Fraction(1, 2**cert.precision)
    )


def independent_interval_stability(
    first: IntervalCertificate,
    second: IntervalCertificate,
    target: Fraction,
) -> bool:
    """Check the cross-certificate stability estimate.

    Independent enclosures of the same target need not have compatible
    witnesses.  Their midpoints are nevertheless close, with an explicit bound
    derived only from the two widths.
    """

    if not interval_valid(first, target) or not interval_valid(second, target):
        return False
    bound = (first.width + second.width) / 2
    return abs(first.midpoint - second.midpoint) <= bound


@dataclass(frozen=True)
class BisectionStep:
    index: int
    lower: Fraction
    upper: Fraction
    midpoint: Fraction
    midpoint_value: Fraction

    def as_json(self) -> dict[str, str | int]:
        return {
            "index": self.index,
            "lower": str(self.lower),
            "upper": str(self.upper),
            "midpoint": str(self.midpoint),
            "midpoint_value": str(self.midpoint_value),
        }


def cubic_value(y: Fraction) -> Fraction:
    """The strictly increasing polynomial ``y^3+y``."""

    return y * y * y + y


def cubic_bisection(
    x: Fraction,
    precision: int,
    lower: Fraction,
    upper: Fraction,
) -> tuple[Fraction, Fraction, tuple[BisectionStep, ...]]:
    """Exact bisection for the unique solution of ``y^3+y=x``.

    The caller supplies a rational sign bracket.  Exactly ``precision`` steps
    are performed, so the fuel is explicit and primitive recursive.
    """

    _require_nonnegative("precision", precision)
    if lower > upper:
        raise ValueError("lower endpoint exceeds upper endpoint")
    if cubic_value(lower) > x or cubic_value(upper) < x:
        raise ValueError("the supplied interval is not a sign bracket")

    lo = lower
    hi = upper
    trace: list[BisectionStep] = []
    for index in range(precision):
        mid = (lo + hi) / 2
        value = cubic_value(mid)
        trace.append(BisectionStep(index, lo, hi, mid, value))
        if value <= x:
            lo = mid
        else:
            hi = mid
    return lo, hi, tuple(trace)


def verify_cubic_bisection(
    x: Fraction,
    precision: int,
    initial_lower: Fraction,
    initial_upper: Fraction,
    final_lower: Fraction,
    final_upper: Fraction,
    trace: Sequence[BisectionStep],
) -> bool:
    """Verify every local transition and the terminal width bound."""

    if len(trace) != precision:
        return False
    lo = initial_lower
    hi = initial_upper
    if cubic_value(lo) > x or cubic_value(hi) < x:
        return False
    for index, step in enumerate(trace):
        if (
            step.index != index
            or step.lower != lo
            or step.upper != hi
            or step.midpoint != (lo + hi) / 2
            or step.midpoint_value != cubic_value(step.midpoint)
        ):
            return False
        if step.midpoint_value <= x:
            lo = step.midpoint
        else:
            hi = step.midpoint
    if (lo, hi) != (final_lower, final_upper):
        return False
    expected_width = (initial_upper - initial_lower) / (2**precision)
    return (
        cubic_value(lo) <= x <= cubic_value(hi)
        and hi - lo == expected_width
    )


def reverse_pipeline_demand(
    terminal_demand: int, transformers: Sequence[Callable[[int], int]]
) -> tuple[int, ...]:
    """Propagate a scalar precision demand backward through a fixed pipeline.

    The returned tuple lists the demand at each interface, including the input
    and terminal interfaces.  Every transformer must be monotone only if a
    separate theorem uses monotonicity; the algorithm itself merely evaluates
    the fixed functions.
    """

    _require_nonnegative("terminal_demand", terminal_demand)
    demands = [terminal_demand]
    current = terminal_demand
    for transformer in reversed(transformers):
        current = transformer(current)
        _require_nonnegative("transformed demand", current)
        demands.append(current)
    demands.reverse()
    return tuple(demands)
