"""Exact finite reference algorithms for FIBER-iPRA.

This module is executable evidence only.  It is not an iPRA proof checker and
it does not replace the `Prf PRAAx` derivations described in the report.
All arithmetic is exact and uses only the Python standard library.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable, Iterable, Mapping, Sequence


class FiberError(ValueError):
    """Raised when finite certificate data violate a declared contract."""


def mixed_radix_encode(values: Sequence[int], bounds: Sequence[int]) -> int:
    """Encode 0 <= values[i] < bounds[i] in one natural number."""
    if len(values) != len(bounds):
        raise FiberError("values and bounds must have the same length")
    code = 0
    place = 1
    for value, bound in zip(values, bounds, strict=True):
        if bound <= 0:
            raise FiberError("every radix bound must be positive")
        if not 0 <= value < bound:
            raise FiberError(f"value {value} is outside radix {bound}")
        code += value * place
        place *= bound
    return code


def mixed_radix_decode(code: int, bounds: Sequence[int]) -> tuple[int, ...]:
    """Decode a code with the supplied radices; reject out-of-range codes."""
    if code < 0:
        raise FiberError("code must be nonnegative")
    total = 1
    for bound in bounds:
        if bound <= 0:
            raise FiberError("every radix bound must be positive")
        total *= bound
    if code >= total:
        raise FiberError(f"code {code} is not below product bound {total}")
    out: list[int] = []
    rest = code
    for bound in bounds:
        out.append(rest % bound)
        rest //= bound
    return tuple(out)


def least_accepted(bound: int, verifier: Callable[[int], bool]) -> int | None:
    """Return the least accepted code below bound, or None if none exists."""
    if bound < 0:
        raise FiberError("bound must be nonnegative")
    for candidate in range(bound):
        if verifier(candidate):
            return candidate
    return None


def master_certificate(
    bounds: Sequence[int], verifiers: Sequence[Callable[[int], bool]]
) -> tuple[int, tuple[int, ...]]:
    """Choose the least valid local code in every finite fiber and bundle it."""
    if len(bounds) != len(verifiers):
        raise FiberError("bounds and verifiers must have the same length")
    witnesses: list[int] = []
    for index, (bound, verifier) in enumerate(zip(bounds, verifiers, strict=True)):
        witness = least_accepted(bound, verifier)
        if witness is None:
            raise FiberError(f"fiber {index} has no accepted code below {bound}")
        witnesses.append(witness)
    code = mixed_radix_encode(witnesses, bounds)
    return code, tuple(witnesses)


def componentwise_join(left: Sequence[int], right: Sequence[int]) -> tuple[int, ...]:
    if len(left) != len(right):
        raise FiberError("vectors must have equal length")
    return tuple(max(x, y) for x, y in zip(left, right, strict=True))


def vector_le(left: Sequence[int], right: Sequence[int]) -> bool:
    return len(left) == len(right) and all(
        x <= y for x, y in zip(left, right, strict=True)
    )


@dataclass(frozen=True)
class DemandClosure:
    capacities: tuple[int, ...]
    history: tuple[tuple[int, ...], ...]
    fixed_point: tuple[int, ...]

    @property
    def potential_bound(self) -> int:
        return sum(self.capacities)

    @property
    def iterations(self) -> int:
        return len(self.history) - 1


def finite_demand_closure(
    capacities: Sequence[int], step: Callable[[tuple[int, ...]], Sequence[int]]
) -> DemandClosure:
    """Iterate d <- d join step(d) through the sum-of-capacities bound.

    The caller is responsible for the mathematical monotonicity proof.  This
    executable function checks only range preservation and the promised finite
    stabilization bound.
    """
    caps = tuple(capacities)
    if any(cap < 0 for cap in caps):
        raise FiberError("capacities must be nonnegative")
    current = tuple(0 for _ in caps)
    history = [current]
    for _ in range(sum(caps) + 1):
        raw = tuple(step(current))
        if len(raw) != len(caps):
            raise FiberError("demand step changed vector dimension")
        if any(not 0 <= value <= cap for value, cap in zip(raw, caps, strict=True)):
            raise FiberError("demand step escaped a coordinate cap")
        nxt = componentwise_join(current, raw)
        if nxt == current:
            return DemandClosure(caps, tuple(history), current)
        if sum(nxt) <= sum(current):
            raise FiberError("a nonfixed update failed to increase the potential")
        history.append(nxt)
        current = nxt
    raise FiberError("demand did not stabilize within the finite potential bound")


def check_monotone_on_finite_lattice(
    capacities: Sequence[int], step: Callable[[tuple[int, ...]], Sequence[int]]
) -> bool:
    """Exhaustively check monotonicity for a small finite product lattice."""
    caps = tuple(capacities)
    points = list(product(*(range(cap + 1) for cap in caps)))
    images = {point: tuple(step(point)) for point in points}
    for point, image in images.items():
        if len(image) != len(caps):
            return False
        if any(not 0 <= value <= cap for value, cap in zip(image, caps, strict=True)):
            return False
    return all(
        not vector_le(x, y) or vector_le(images[x], images[y])
        for x in points
        for y in points
    )


@dataclass(frozen=True)
class Quantifier:
    kind: str  # "forall" or "exists"
    bound: Callable[[tuple[int, ...]], int]


Strategy = Mapping[tuple[int, ...], int]


def verify_bounded_strategy(
    quantifiers: Sequence[Quantifier],
    strategy: Strategy,
    leaf: Callable[[tuple[int, ...]], bool],
) -> bool:
    """Verify a finite strategy certificate for a fixed quantifier prefix."""

    def visit(depth: int, history: tuple[int, ...]) -> bool:
        if depth == len(quantifiers):
            return bool(leaf(history))
        quantifier = quantifiers[depth]
        bound = quantifier.bound(history)
        if bound < 0:
            raise FiberError("strategy bound must be nonnegative")
        if quantifier.kind == "forall":
            return all(visit(depth + 1, history + (move,)) for move in range(bound))
        if quantifier.kind == "exists":
            if history not in strategy:
                return False
            move = strategy[history]
            return 0 <= move < bound and visit(depth + 1, history + (move,))
        raise FiberError(f"unknown quantifier kind {quantifier.kind!r}")

    return visit(0, ())


def dyadic_scaled_discrepancy(numerators: Sequence[int], n: int, m: int) -> int:
    """Return |2^(m-n) a_n - a_m| for m >= n."""
    if not 0 <= n <= m < len(numerators):
        raise FiberError("indices must satisfy 0 <= n <= m < len")
    return abs((1 << (m - n)) * numerators[n] - numerators[m])


def verify_dyadic_adjacent_motion(numerators: Sequence[int]) -> bool:
    """Check |2 a_k - a_(k+1)| <= 1 at every adjacent pair."""
    return all(
        abs(2 * numerators[k] - numerators[k + 1]) <= 1
        for k in range(len(numerators) - 1)
    )


def verify_dyadic_cauchy_bound(numerators: Sequence[int]) -> bool:
    """Check the exact bound Delta(n,m) <= 2^(m-n)-1 for all pairs."""
    if not verify_dyadic_adjacent_motion(numerators):
        return False
    for n in range(len(numerators)):
        for m in range(n, len(numerators)):
            if dyadic_scaled_discrepancy(numerators, n, m) > (1 << (m - n)) - 1:
                return False
    return True


def dyadic_value(numerator: int, precision: int) -> Fraction:
    return Fraction(numerator, 1 << precision)


@dataclass(frozen=True)
class NetCertificate:
    points: tuple[Fraction, ...]
    epsilon: Fraction

    def cover_index(self, x: Fraction) -> int | None:
        return least_accepted(len(self.points), lambda i: abs(x - self.points[i]) <= self.epsilon)


def finite_net_lift(
    domain: Iterable[Fraction],
    net: NetCertificate,
    f: Callable[[Fraction], Fraction],
    modulus_delta: Fraction,
    local_bound: Fraction,
) -> dict[Fraction, tuple[int, Fraction]]:
    """Seal a local cover index and return the lifted bound for each point.

    Contract checked by this reference routine:
      * every domain point lies within epsilon of a net point;
      * |f(x)-f(z)| <= modulus_delta for the selected point;
      * |f(z)| <= local_bound at every net point.
    The lifted conclusion is |f(x)| <= local_bound + modulus_delta.
    """
    if net.epsilon < 0 or modulus_delta < 0 or local_bound < 0:
        raise FiberError("bounds must be nonnegative")
    for z in net.points:
        if abs(f(z)) > local_bound:
            raise FiberError("a net-point local bound failed")
    result: dict[Fraction, tuple[int, Fraction]] = {}
    for x in domain:
        index = net.cover_index(x)
        if index is None:
            raise FiberError(f"net does not cover {x}")
        z = net.points[index]
        if abs(f(x) - f(z)) > modulus_delta:
            raise FiberError("modulus certificate failed")
        lifted = local_bound + modulus_delta
        if abs(f(x)) > lifted:
            raise FiberError("triangle-inequality lift failed")
        result[x] = (index, lifted)
    return result


def bisection_trace(
    polynomial: Callable[[Fraction], Fraction],
    left: Fraction,
    right: Fraction,
    steps: int,
) -> tuple[tuple[Fraction, Fraction], ...]:
    """Produce an exact rational sign-bracketing bisection trace."""
    if steps < 0:
        raise FiberError("steps must be nonnegative")
    if not polynomial(left) <= 0 <= polynomial(right):
        raise FiberError("initial interval is not sign-bracketing")
    trace = [(left, right)]
    for _ in range(steps):
        midpoint = (left + right) / 2
        value = polynomial(midpoint)
        if value <= 0:
            left = midpoint
        else:
            right = midpoint
        if not polynomial(left) <= 0 <= polynomial(right):
            raise FiberError("bisection invariant failed")
        trace.append((left, right))
    return tuple(trace)


def verify_bisection_trace(
    polynomial: Callable[[Fraction], Fraction],
    trace: Sequence[tuple[Fraction, Fraction]],
) -> bool:
    if not trace:
        return False
    initial_width = trace[0][1] - trace[0][0]
    for index, (left, right) in enumerate(trace):
        if not left <= right:
            return False
        if not polynomial(left) <= 0 <= polynomial(right):
            return False
        if right - left != initial_width / (1 << index):
            return False
        if index > 0:
            pleft, pright = trace[index - 1]
            midpoint = (pleft + pright) / 2
            if (left, right) not in ((pleft, midpoint), (midpoint, pright)):
                return False
    return True


def herbrand_capsule(candidates: Sequence[int], relation: Callable[[int], bool]) -> tuple[int, ...]:
    """Return a finite candidate list after checking that at least one is valid."""
    capsule = tuple(candidates)
    if not any(relation(candidate) for candidate in capsule):
        raise FiberError("capsule contains no valid candidate")
    return capsule


def least_valid_in_capsule(capsule: Sequence[int], relation: Callable[[int], bool]) -> int:
    index = least_accepted(len(capsule), lambda i: relation(capsule[i]))
    if index is None:
        raise FiberError("capsule contains no valid candidate")
    return capsule[index]
