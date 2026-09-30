#!/usr/bin/env python3
"""Exact finite certificates accompanying the convolution-divisor article.

Python 3.10+; standard library only. No network access is used.
Finite computations test implementations and examples, not infinite theorems.
Run: python verify.py --output verification.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


class ResourceLimitError(RuntimeError):
    """A finite test was not attempted; this never means mathematical failure."""


def require_int(value: int, name: str, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def require_prime(p: int) -> int:
    require_int(p, "p", 2)
    if any(p % d == 0 for d in range(2, math.isqrt(p) + 1)):
        raise ValueError("p must be prime")
    return p


def valuation(n: int, p: int) -> int:
    """Exponent of p in a positive integer; caller may validate p once."""
    require_int(n, "n", 1)
    require_int(p, "p", 2)
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def finite_certificate(p: int, denominators: Sequence[int],
                       power: int = 1) -> dict:
    """Certify uniform factors of X_(p**power); return a matching or a pole.

    Entry j denotes the width 1/denominators[j]. A matching assigns one
    distinct supply slot k with (p**power)**k dividing that denominator.
    """
    require_prime(p)
    require_int(power, "power", 1)
    ns = [require_int(n, "denominator", 1) for n in denominators]
    order = sorted(range(len(ns)), key=lambda j: (valuation(ns[j], p) // power, j))
    matching = []
    for k, j in enumerate(order):
        deadline = valuation(ns[j], p) // power
        if deadline < k:
            selected = order[:k + 1]
            m = math.lcm(*(ns[i] for i in selected))
            target_order = 1 + valuation(m, p) // power
            source_order = sum(m % n == 0 for n in ns)
            assert source_order > target_order
            return {"accepted": False, "deadline": deadline,
                    "selected_indices": selected, "zero_over_pi": m,
                    "target_zero_order": target_order,
                    "source_zero_order": source_order}
        supply_divisor = p ** (power * k)
        assert ns[j] % supply_divisor == 0
        matching.append({"source_index": j, "slot": k,
                         "digit_count": ns[j] // supply_divisor})
    return {"accepted": True, "matching": matching}


@dataclass(frozen=True, order=True)
class Stream:
    """An infinite sequence of p-adic deadlines start + step*j."""
    start: int
    step: int

    def __post_init__(self) -> None:
        require_int(self.start, "start", 0)
        require_int(self.step, "step", 1)


def demand(k: int, streams: Sequence[Stream], finite: Sequence[int] = ()) -> int:
    if k < 0:
        return 0
    return (sum(d <= k for d in finite)
            + sum(max(0, (k - s.start) // s.step + 1) for s in streams))


def stream_certificate(streams: Sequence[Stream], finite: Sequence[int] = (),
                       max_period: int = 100_000,
                       max_checks: int = 1_000_000) -> dict:
    """Decide ALL Hall inequalities for finitely many arithmetic streams.

    'finite' contains deadlines, not the original integer denominators.
    The method is exact but not polynomial in binary input length: the
    least common multiple can be large. Resource limits raise an exception.
    """
    fs = [require_int(d, "finite deadline", 0) for d in finite]
    if not all(isinstance(s, Stream) for s in streams):
        raise TypeError("streams must contain Stream objects")
    require_int(max_period, "max_period", 1)
    require_int(max_checks, "max_checks", 1)
    period = 1
    for s in streams:
        period = math.lcm(period, s.step)
        if period > max_period:
            raise ResourceLimitError("LCM exceeds max_period; no decision made")
    threshold = max([0, *fs, *(s.start for s in streams)])
    if threshold + period > max_checks:
        raise ResourceLimitError("Finite window exceeds max_checks; no decision made")
    drift = period - sum(period // s.step for s in streams)
    slack = [k + 1 - demand(k, streams, fs) for k in range(threshold + period)]
    result = {"period": period, "threshold": threshold, "drift": drift,
              "density_surplus": str(Fraction(drift, period)),
              "finite_slacks": slack}
    bad = next((k for k, value in enumerate(slack) if value < 0), None)
    if bad is None and drift < 0:
        q = slack[threshold] // (-drift) + 1
        bad = threshold + q * period
    if bad is not None:
        count = demand(bad, streams, fs)
        assert count > bad + 1
        return {**result, "accepted": False, "witness_K": bad,
                "witness_demand": count, "witness_capacity": bad + 1}
    return {**result, "accepted": True}


def brute_matching(p: int, power: int, ns: Sequence[int]) -> bool:
    """Independent small backtracking oracle, without sorting deadlines."""
    def go(j: int, available: tuple[int, ...]) -> bool:
        if j == len(ns):
            return True
        return any(ns[j] % (p ** (power * k)) == 0
                   and go(j + 1, tuple(q for q in available if q != k))
                   for k in available)
    return go(0, tuple(range(len(ns))))


def subset_zero_oracle(p: int, power: int, ns: Sequence[int]) -> bool:
    """Check multiplicity at every nonempty subfamily's least common multiple."""
    for size in range(1, len(ns) + 1):
        for sub in itertools.combinations(ns, size):
            m = math.lcm(*sub)
            if sum(m % n == 0 for n in ns) > 1 + valuation(m, p) // power:
                return False
    return True


def convolution(a: dict[int, int], b: dict[int, int]) -> dict[int, int]:
    out: dict[int, int] = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i + j] = out.get(i + j, 0) + x * y
    return {i: x for i, x in out.items() if x}


def uniform_moment(radius: Fraction, k: int) -> Fraction:
    return Fraction(0) if k % 2 else radius ** k / (k + 1)


def run_tests() -> dict:
    counts: dict[str, int] = {}
    accepted = 0
    finite_cases = 0
    for p, power in [(2, 1), (3, 1), (5, 1), (2, 2), (3, 2)]:
        for size in range(5):
            for ns in itertools.combinations_with_replacement(range(1, 13), size):
                cert = finite_certificate(p, ns, power)
                assert cert["accepted"] == brute_matching(p, power, ns)
                assert cert["accepted"] == subset_zero_oracle(p, power, ns)
                finite_cases += 1
                accepted += cert["accepted"]
    counts["finite_families_checked"] = finite_cases
    counts["finite_families_accepted"] = accepted

    moments_checked = 0
    partitions_checked = 0
    for p in [2, 3, 5]:
        for k in range(4):
            for r in range(1, 9):
                n = r * p ** k
                a, b = Fraction(1, p ** k), Fraction(1, n)
                centers = [Fraction(2 * ell - r + 1, n) for ell in range(r)]
                assert centers[0] - b == -a and centers[-1] + b == a
                assert all(centers[i] + b == centers[i + 1] - b
                           for i in range(r - 1))
                partitions_checked += 1
                for degree in range(11):
                    value = sum(Fraction(math.comb(degree, j)) * uniform_moment(b, j)
                                * sum(c ** (degree - j) for c in centers) / r
                                for j in range(degree + 1))
                    assert value == uniform_moment(a, degree)
                    moments_checked += 1
    counts["uniform_partitions_checked"] = partitions_checked
    counts["exact_moment_identities_checked"] = moments_checked

    available = [Stream(a, s) for a in range(5) for s in range(1, 5)]
    stream_cases = 0
    recurrence_checks = 0
    accepted_streams = 0
    for size in range(4):
        for streams in itertools.combinations_with_replacement(available, size):
            for fs in [(), (0,), (1,), (0, 2), (3,)]:
                cert = stream_certificate(streams, fs)
                stop = max(257, cert.get("witness_K", 0) + 1)
                brute = all(demand(k, streams, fs) <= k + 1 for k in range(stop))
                assert cert["accepted"] == brute
                a, period, drift = cert["threshold"], cert["period"], cert["drift"]
                for k in range(a, a + 3 * period):
                    f0 = k + 1 - demand(k, streams, fs)
                    f1 = k + period + 1 - demand(k + period, streams, fs)
                    assert f1 - f0 == drift
                    recurrence_checks += 1
                accepted_streams += cert["accepted"]
                stream_cases += 1
    counts["stream_families_checked"] = stream_cases
    counts["stream_families_accepted"] = accepted_streams
    counts["exact_period_recurrences_checked"] = recurrence_checks

    # cos(3u) = cos(u) * (2 cos(2u) - 1), in Laurent polynomials.
    assert convolution({1: 1, -1: 1}, {2: 1, -2: 1, 0: -1}) == {3: 1, -3: 1}
    tau_radius = Fraction(6, 5) / 36
    assert tau_radius == Fraction(1, 30)
    assert 2 * tau_radius < Fraction(1, 3)
    counts["composite_base_laurent_identities_checked"] = 1

    # Deliberate input and resource errors must not become rejection certificates.
    validation_cases = 0
    for operation in [lambda: finite_certificate(4, [1]),
                      lambda: finite_certificate(2, [0]),
                      lambda: Stream(0, 0),
                      lambda: stream_certificate([Stream(0, 101)], max_period=100)]:
        try:
            operation()
        except (ValueError, ResourceLimitError):
            validation_cases += 1
        else:
            raise AssertionError("Expected validation exception")
    counts["validation_cases_checked"] = validation_cases

    specs = {
        "two_unshifted_base4": ([Stream(0, 2), Stream(0, 2)], ()),
        "interleaved_base4": ([Stream(0, 2), Stream(1, 2)], ()),
        "two_half_scaled_base4": ([Stream(1, 2), Stream(1, 2)], ()),
        "two_quarter_scaled_base4": ([Stream(2, 2), Stream(2, 2)], ()),
        "two_eighth_scaled_base4": ([Stream(3, 2), Stream(3, 2)], ()),
        "one_base4": ([Stream(0, 2)], ()),
        "finite_digit_residual": ([Stream(1, 1)], (1,)),
    }
    examples = {}
    for name, (streams, fs) in specs.items():
        cert = stream_certificate(streams, fs)
        examples[name] = {"streams": [[s.start, s.step] for s in streams],
                          "finite_deadlines": list(fs), "certificate": cert,
                          "g_1_through_16": [h - demand(h - 1, streams, fs)
                                             for h in range(1, 17)]}
    return {
        "status": "all tests passed",
        "scope": "Exact finite tests and certificate examples, not formal verification of analytic theorems.",
        "counts": counts,
        "examples": examples,
        "composite_base6": {"tau_radius": str(tau_radius),
                            "signed_mass_on_central_interval": -1},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    result = run_tests()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], **result["counts"]}, indent=2))


if __name__ == "__main__":
    main()
