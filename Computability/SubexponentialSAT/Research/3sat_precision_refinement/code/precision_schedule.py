#!/usr/bin/env python3
"""Exact reference schedules for tapered Hermite recovery.

This module implements a proved parameter refinement of the Cauchy/Hermite
step in OpenAI's October 25, 2026 preprint.  It is not a SAT solver and makes
no claim to improve the power of log n in the published running-time order.

All schedule computations use Python integers or fractions.Fraction.  The
linear strategy uses the least integer slope that supplies enough Hermite
data.  The equal-loss and finite-optimal strategies round exact real optima
upward; they are not claimed to solve the integer minimax problem exactly.

Example:
    python3 precision_schedule.py --wires 1000 --packet-exponent 12 \
        --levels 6 --input-precision 1001 --strategy linear

Reference: ../notes/hermite_precision_refinement.md.  The baseline preprint
is pinned at commit 42907c9e999cc00d6abe7a50bfc1023250edd1b9.
Standard library only; Python 3.10 or newer.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from typing import Sequence


SOURCE_COMMIT = "42907c9e999cc00d6abe7a50bfc1023250edd1b9"


def ceiling(value: int | Fraction) -> int:
    """Exact ceiling, without conversion to float."""
    value = Fraction(value)
    return -(-value.numerator // value.denominator)


def _require_integer(name: str, value: int, minimum: int = 0) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def validate_parameters(wires: int, packet_exponent: int, levels: int, input_precision: int) -> None:
    for name, value in (("wires", wires), ("packet_exponent", packet_exponent),
                        ("levels", levels), ("input_precision", input_precision)):
        _require_integer(name, value, 1)
    if packet_exponent < levels:
        raise ValueError("packet_exponent must be at least levels")
    if wires < levels:
        raise ValueError("wires must be at least levels")


def finite_loss_numerators(packet_exponent: int, taper: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
    """Compute B_i exactly, extending the supplied taper by zero.

    B_i = sum_{j=1}^{a-i} j*2**(a-i-j)*(q_i-q_(i+j)).

    The function also accepts rational tapers for auditing the real optima.
    A nonnegative nonincreasing taper has nonnegative losses.
    """
    _require_integer("packet_exponent", packet_exponent, 1)
    q = tuple(Fraction(value) for value in taper)
    if not q or len(q) > packet_exponent:
        raise ValueError("taper length must be between one and packet_exponent")
    if any(value < 0 for value in q):
        raise ValueError("multiplicities cannot be negative")
    losses = []
    for index, value in enumerate(q):
        loss = sum(
            Fraction(j * (1 << (packet_exponent - index - j)))
            * (value - (q[index + j] if index + j < len(q) else 0))
            for j in range(1, packet_exponent - index + 1)
        )
        losses.append(loss)
    return tuple(losses)


def full_normalized_losses(taper: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
    """Compute the infinite-tail losses with the exact zero-tail sum."""
    q = tuple(Fraction(value) for value in taper)
    return tuple(
        2 * q[index] - sum(Fraction(j, 1 << j) * q[index + j]
                          for j in range(1, len(q) - index))
        for index in range(len(q))
    )


def weighted_multiplicity(taper: Sequence[int | Fraction]) -> Fraction:
    """Return sum_i 2**(-i) q_i, without its common factor L."""
    return sum((Fraction(value, 1 << index) for index, value in enumerate(taper)), Fraction(0))


@dataclass(frozen=True)
class PrecisionSchedule:
    wires: int
    packet_exponent: int
    levels: int
    input_precision: int
    strategy: str
    multiplicities: tuple[int, ...]
    losses: tuple[int, ...]
    exact_sufficient_precisions: tuple[int | None, ...]
    working_precisions: tuple[int | None, ...]
    real_multiplicities: tuple[Fraction, ...] | None = None
    real_optimal_normalized_loss: Fraction | None = None

    @property
    def packet_length(self) -> int:
        return 1 << self.packet_exponent

    @property
    def degree_bound(self) -> int:
        return self.wires * (2 * self.packet_length - 1)

    @property
    def total_multiplicity(self) -> int:
        return sum((1 << (self.packet_exponent - index)) * q
                   for index, q in enumerate(self.multiplicities))

    @property
    def normalized_losses(self) -> tuple[Fraction, ...]:
        return tuple(Fraction(loss, 1 << (self.packet_exponent - index))
                     for index, loss in enumerate(self.losses))

    def as_dict(self) -> dict:
        def rational(value: Fraction | None):
            return None if value is None else {"numerator": value.numerator, "denominator": value.denominator}

        result = {
            "strategy": self.strategy,
            "wires": self.wires,
            "packet_exponent": self.packet_exponent,
            "packet_length": self.packet_length,
            "levels": self.levels,
            "input_precision": self.input_precision,
            "degree_bound": self.degree_bound,
            "required_total_multiplicity": self.degree_bound + 1,
            "total_multiplicity": self.total_multiplicity,
            "multiplicities_by_valuation_level": list(self.multiplicities),
            "node_counts_by_valuation_level": [1 << (self.packet_exponent - i) for i in range(self.levels)],
            "finite_loss_numerators_B_i": list(self.losses),
            "finite_normalized_losses_B_i_over_D_i": [rational(value) for value in self.normalized_losses],
            "exact_sufficient_precisions_by_level": list(self.exact_sufficient_precisions),
            "working_precisions_by_level": list(self.working_precisions),
            "maximum_working_precision": max(value for value in self.working_precisions if value is not None),
        }
        if self.real_multiplicities is not None:
            result["real_multiplicities_before_rounding"] = [rational(value) for value in self.real_multiplicities]
            result["real_optimal_normalized_loss"] = rational(self.real_optimal_normalized_loss)
            result["integer_optimality_claimed"] = False
        return result


def from_taper(wires: int, packet_exponent: int, levels: int, input_precision: int,
               taper: Sequence[int], *, strategy: str = "custom-monotone",
               working_precisions: Sequence[int | None] | None = None,
               real_multiplicities: tuple[Fraction, ...] | None = None,
               real_optimal_normalized_loss: Fraction | None = None) -> PrecisionSchedule:
    """Validate a complete monotone integer taper and calculate exact losses.

    A zero multiplicity denotes an unused level, whose precision is None.
    Undercomplete profiles and supplied working precisions below the proved
    requirement are rejected.  There is no floating-point safety margin.
    """
    validate_parameters(wires, packet_exponent, levels, input_precision)
    q = tuple(taper)
    if len(q) != levels:
        raise ValueError("taper length differs from levels")
    for value in q:
        _require_integer("multiplicity", value, 0)
    if any(left < right for left, right in zip(q, q[1:])):
        raise ValueError("this reference interface requires a nonincreasing taper")
    length = 1 << packet_exponent
    degree = wires * (2 * length - 1)
    total = sum((1 << (packet_exponent - index)) * value for index, value in enumerate(q))
    if total <= degree:
        raise ValueError("taper does not supply enough Hermite multiplicity")
    rational_losses = finite_loss_numerators(packet_exponent, q)
    if any(loss.denominator != 1 or loss < 0 for loss in rational_losses):
        raise AssertionError("integer monotone taper produced a nonintegral or negative loss")
    losses = tuple(int(loss) for loss in rational_losses)
    sufficient = tuple(
        input_precision + losses[index] + (value - 1) * (packet_exponent + 1 - index)
        if value else None
        for index, value in enumerate(q)
    )
    if working_precisions is None:
        working = sufficient
    else:
        working = tuple(working_precisions)
        if len(working) != levels:
            raise ValueError("working precision length differs from levels")
        for actual, required in zip(working, sufficient):
            if required is None:
                if actual is not None:
                    raise ValueError("inactive levels must have precision None")
            elif not isinstance(actual, int) or actual < required:
                raise ValueError("working precision is below the proved requirement")
    return PrecisionSchedule(wires, packet_exponent, levels, input_precision, strategy,
                             q, losses, sufficient, working, real_multiplicities,
                             real_optimal_normalized_loss)


def source_linear(wires: int, packet_exponent: int, levels: int, input_precision: int) -> PrecisionSchedule:
    """Reproduce the source's h=ceil(3M/u) and its stated precision formula."""
    validate_parameters(wires, packet_exponent, levels, input_precision)
    slope = ceiling(Fraction(3 * wires, levels))
    taper = tuple(slope * (levels - index) for index in range(levels))
    working = tuple(input_precision + 8 * slope * (1 << (packet_exponent - index))
                    + 8 * wires * (packet_exponent + 1) for index in range(levels))
    return from_taper(wires, packet_exponent, levels, input_precision, taper,
                      strategy="source-linear", working_precisions=working)


def optimized_linear(wires: int, packet_exponent: int, levels: int, input_precision: int) -> PrecisionSchedule:
    """Use the least integer complete linear slope and exact sufficient bits."""
    validate_parameters(wires, packet_exponent, levels, input_precision)
    length = 1 << packet_exponent
    denominator = sum((1 << (packet_exponent - index)) * (levels - index)
                      for index in range(levels))
    slope = ceiling(Fraction(wires * (2 * length - 1) + 1, denominator))
    taper = tuple(slope * (levels - index) for index in range(levels))
    return from_taper(wires, packet_exponent, levels, input_precision, taper, strategy="linear")


def rounded_optimal_full(wires: int, packet_exponent: int, levels: int, input_precision: int) -> PrecisionSchedule:
    """Round upward the exact real minimizer of the full-tail minimax loss."""
    validate_parameters(wires, packet_exponent, levels, input_precision)
    length = 1 << packet_exponent
    required_weight = Fraction(wires * (2 * length - 1) + 1, length)
    capacity = Fraction(levels, 3) + Fraction(2, 9) - Fraction(2, 9 * 4 ** levels)
    maximum_loss = required_weight / capacity
    real = tuple(
        maximum_loss * (Fraction(k, 6) + Fraction(5, 18) + Fraction(2, 9 * 4 ** k))
        for k in reversed(range(1, levels + 1))
    )
    taper = tuple(ceiling(value) for value in real)
    return from_taper(wires, packet_exponent, levels, input_precision, taper,
                      strategy="equal-loss", real_multiplicities=real,
                      real_optimal_normalized_loss=maximum_loss)


def finite_optimal(wires: int, packet_exponent: int, levels: int, input_precision: int) -> PrecisionSchedule:
    """Round upward the exact real finite-grid optimum, via a recurrence.

    First solve the triangular loss equations at maximum normalized loss one.
    Then scale to exact Hermite completeness and round up.  This computes the
    real optimum exactly; the rounded integer taper need not be integer-optimal.
    """
    validate_parameters(wires, packet_exponent, levels, input_precision)
    length = 1 << packet_exponent
    required_weight = Fraction(wires * (2 * length - 1) + 1, length)
    profile = [Fraction(0)] * levels
    for index in reversed(range(levels)):
        diagonal = sum((Fraction(j, 1 << j) for j in range(1, packet_exponent - index + 1)), Fraction(0))
        continuation = sum((Fraction(j, 1 << j) * profile[index + j]
                            for j in range(1, levels - index)), Fraction(0))
        profile[index] = (1 + continuation) / diagonal
    maximum_loss = required_weight / weighted_multiplicity(profile)
    real = tuple(maximum_loss * value for value in profile)
    taper = tuple(ceiling(value) for value in real)
    return from_taper(wires, packet_exponent, levels, input_precision, taper,
                      strategy="finite-optimal", real_multiplicities=real,
                      real_optimal_normalized_loss=maximum_loss)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wires", type=int, required=True)
    parser.add_argument("--packet-exponent", type=int, required=True)
    parser.add_argument("--levels", type=int, required=True)
    parser.add_argument("--input-precision", type=int, required=True)
    parser.add_argument("--strategy", choices=("linear", "equal-loss", "finite-optimal"), default="linear")
    args = parser.parse_args()
    strategies = {"linear": optimized_linear, "equal-loss": rounded_optimal_full, "finite-optimal": finite_optimal}
    parameters = (args.wires, args.packet_exponent, args.levels, args.input_precision)
    try:
        chosen = strategies[args.strategy](*parameters)
        source = source_linear(*parameters)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps({
        "artifact_kind": "exact_hermite_precision_schedule",
        "scope": "Reference interpolation schedule; not a complete SAT solver.",
        "source_commit": SOURCE_COMMIT,
        "selected": chosen.as_dict(),
        "source_reference": source.as_dict(),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
