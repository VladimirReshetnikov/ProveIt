#!/usr/bin/env python3
"""Exact reference kernel for the Certified Finitary Presentation framework.

This program is deliberately small and uses only integers and Fraction.
It is a semantic/executable companion to the paper, not an iPRA proof checker.
The object-language formalization must reimplement the same finite recurrences
as primitive-recursive symbols and prove their contracts by quantifier-free
induction.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json
import math
from pathlib import Path
from typing import Callable, Iterable, Sequence


class CertificateError(ValueError):
    """Raised when a finite certificate fails validation."""


def dyadic(k: int) -> Fraction:
    if k < 0:
        raise ValueError("precision must be nonnegative")
    return Fraction(1, 1 << k)


def absq(x: Fraction) -> Fraction:
    return x if x >= 0 else -x


def polynomial_eval(coefficients: Sequence[int], x: Fraction) -> Fraction:
    """Evaluate c[0] + c[1] x + ... by Horner's rule."""
    value = Fraction(0)
    for c in reversed(coefficients):
        value = value * x + c
    return value


def polynomial_lipschitz(coefficients: Sequence[int], bound: int) -> int:
    """Integer majorant for |P(x)-P(y)|/|x-y| on |x|,|y| <= bound."""
    if bound < 1:
        raise ValueError("bound must be at least 1")
    total = 0
    for degree, coefficient in enumerate(coefficients):
        if degree:
            total += abs(coefficient) * degree * (bound ** (degree - 1))
    return total


@dataclass(frozen=True)
class TraceCertificate:
    input_code: int
    bound: int
    initial_state: int
    states: tuple[int, ...]
    final_claim: int


def verify_trace(
    cert: TraceCertificate,
    step: Callable[[int, int, int], int],
    invariant: Callable[[int, int, int], bool],
    accept: Callable[[int, int], int],
) -> None:
    """Check a bounded recurrence and a Boolean invariant at every stage."""
    if cert.bound < 0:
        raise CertificateError("negative trace bound")
    if len(cert.states) != cert.bound + 1:
        raise CertificateError("trace has wrong number of states")
    if cert.states[0] != cert.initial_state:
        raise CertificateError("initial state mismatch")
    for i, state in enumerate(cert.states):
        if not invariant(cert.input_code, i, state):
            raise CertificateError(f"invariant fails at stage {i}")
        if i < cert.bound:
            expected = step(cert.input_code, i, state)
            if cert.states[i + 1] != expected:
                raise CertificateError(f"step mismatch at stage {i}")
    observed = accept(cert.input_code, cert.states[-1])
    if observed != cert.final_claim:
        raise CertificateError("final claim mismatch")


@dataclass(frozen=True)
class RobustDecision:
    branch: str
    lower: Fraction | None
    upper: Fraction | None


def overlapping_branch(
    approximation: Fraction,
    error: Fraction,
    threshold: Fraction,
    overlap: Fraction,
) -> RobustDecision:
    """Decide x < q+overlap or x > q from |x-approximation| <= error.

    The decision is valid when 4*error <= overlap.  The two conclusions
    overlap; this is the constructive substitute for exact trichotomy.
    """
    if error < 0 or overlap <= 0 or 4 * error > overlap:
        raise ValueError("need nonnegative error and 4*error <= overlap")
    if approximation <= threshold + overlap / 2:
        return RobustDecision("upper", None, threshold + overlap)
    return RobustDecision("lower", threshold, None)


def exact_branch_with_gap(
    approximation: Fraction,
    error: Fraction,
    threshold: Fraction,
    gap: Fraction,
) -> str:
    """Determine the exact side when |x-threshold| >= gap and error < gap/2."""
    if gap <= 0 or error < 0 or 2 * error >= gap:
        raise ValueError("need gap>0 and 2*error<gap")
    if approximation > threshold:
        return "above"
    if approximation < threshold:
        return "below"
    raise CertificateError("approximation at threshold contradicts the promised gap")


@dataclass(frozen=True)
class NetWitness:
    numerator: int
    denominator: int
    point: Fraction
    residual: Fraction


def finite_grid_minimum(
    coefficients: Sequence[int],
    left: Fraction,
    right: Fraction,
    denominator: int,
) -> NetWitness:
    """Find a grid point minimizing |P| on [left,right], exactly."""
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    start = math.ceil(left * denominator)
    stop = math.floor(right * denominator)
    if start > stop:
        raise ValueError("grid has no points in interval")
    best_n = start
    best_x = Fraction(start, denominator)
    best_r = absq(polynomial_eval(coefficients, best_x))
    for n in range(start + 1, stop + 1):
        x = Fraction(n, denominator)
        r = absq(polynomial_eval(coefficients, x))
        if r < best_r or (r == best_r and n < best_n):
            best_n, best_x, best_r = n, x, r
    return NetWitness(best_n, denominator, best_x, best_r)


def sqrt2_interval(k: int) -> tuple[Fraction, Fraction]:
    """A dyadic interval of width 2^-k containing sqrt(2)."""
    if k < 0:
        raise ValueError("precision must be nonnegative")
    scale = 1 << k
    n = math.isqrt(2 * scale * scale)
    lo = Fraction(n, scale)
    hi = Fraction(n + 1, scale)
    assert lo * lo <= 2 < hi * hi
    return lo, hi


def sqrt2_midpoint(k: int) -> Fraction:
    lo, hi = sqrt2_interval(k + 1)
    return (lo + hi) / 2


def finite_regularity_check(
    approximator: Callable[[int], Fraction], max_precision: int, slack_bits: int = 0
) -> None:
    """Finite regression check of the regular-name inequality."""
    if max_precision < 0 or slack_bits < 0:
        raise ValueError("nonnegative parameters required")
    for k in range(max_precision + 1):
        for l in range(max_precision + 1):
            lhs = absq(approximator(k) - approximator(l))
            rhs = dyadic(k + slack_bits) + dyadic(l + slack_bits)
            if lhs > rhs:
                raise CertificateError(f"regularity fails at ({k},{l})")


def height_bound_to_list(
    parameter: int,
    bound: int,
    predicate: Callable[[int, int], bool],
) -> list[int]:
    """Complete finite list when code height is the code itself."""
    if bound < 0:
        raise ValueError("negative height bound")
    return [x for x in range(bound + 1) if predicate(parameter, x)]


def list_to_height_bound(points: Iterable[int]) -> int:
    values = list(points)
    if any(x < 0 for x in values):
        raise ValueError("codes must be natural numbers")
    return max(values, default=0)


def load_certificate(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if data.get("schema") != "cfp-framework-certificate-v1":
        raise CertificateError("unknown certificate schema")
    return data


def verify_framework_certificate(data: dict) -> dict:
    trace_data = data["trace_demo"]
    trace = TraceCertificate(
        input_code=int(trace_data["input_code"]),
        bound=int(trace_data["bound"]),
        initial_state=int(trace_data["initial_state"]),
        states=tuple(int(x) for x in trace_data["states"]),
        final_claim=int(trace_data["final_claim"]),
    )
    verify_trace(
        trace,
        step=lambda u, i, s: s + u + i,
        invariant=lambda u, i, s: s == i * u + i * (i - 1) // 2,
        accept=lambda _u, s: s,
    )

    branch_data = data["robust_branch_demo"]
    approx = Fraction(branch_data["approx_num"], branch_data["approx_den"])
    error = Fraction(branch_data["error_num"], branch_data["error_den"])
    threshold = Fraction(branch_data["threshold_num"], branch_data["threshold_den"])
    overlap = Fraction(branch_data["overlap_num"], branch_data["overlap_den"])
    decision = overlapping_branch(approx, error, threshold, overlap)
    if decision.branch != branch_data["expected_branch"]:
        raise CertificateError("robust branch differs from certificate")

    net_data = data["finite_net_demo"]
    witness = finite_grid_minimum(
        [int(c) for c in net_data["coefficients"]],
        Fraction(net_data["left_num"], net_data["left_den"]),
        Fraction(net_data["right_num"], net_data["right_den"]),
        int(net_data["denominator"]),
    )
    if witness.numerator != int(net_data["expected_numerator"]):
        raise CertificateError("finite-net minimizer differs from certificate")
    if witness.residual != Fraction(net_data["expected_residual_num"], net_data["expected_residual_den"]):
        raise CertificateError("finite-net residual differs from certificate")

    finite_regularity_check(sqrt2_midpoint, int(data["sqrt2_regularity_max_precision"]), slack_bits=0)

    return {
        "trace_final": trace.final_claim,
        "robust_branch": decision.branch,
        "net_point": str(witness.point),
        "net_residual": str(witness.residual),
        "sqrt2_regularity_checked_through": int(data["sqrt2_regularity_max_precision"]),
    }


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = verify_framework_certificate(load_certificate(args.certificate))
    text = json.dumps(report, indent=2, sort_keys=True)
    print(text)
    if args.report:
        args.report.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
