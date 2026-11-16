#!/usr/bin/env python3
"""Exact finite checks for fixed-dimensional lexicographic fuel.

Only Python's standard library is used.  These checks validate examples,
index conventions and the sharp-chain construction.  They are not a proof
of the universal theorems and are not object-iPRA proof certificates.

`make_fixed_depth_fuel(d, h)` is a metalevel generator for the particular
fixed-dimensional definition F_d.  No claim is made that evaluation with
unrestricted d is primitive recursive.  The report proves the opposite for
a simple envelope.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


NatFunction = Callable[[int], int]
Rank = tuple[int, ...]


def iterate(function: NatFunction, count: int, value: int) -> int:
    """Exact finite iteration; its function argument is fixed by a caller."""
    if count < 0 or value < 0:
        raise ValueError("Natural-number arguments are required")
    for _ in range(count):
        value = function(value)
    return value


def make_fixed_depth_fuel(dimension: int, envelope: NatFunction) -> NatFunction:
    """Generate F_d(s), where F_0(s)=s+1 and F_(d+1)=F_d^[h(s)+1](s)."""
    if dimension < 0:
        raise ValueError("The dimension must be a natural number")

    def successor(start: int) -> int:
        return start + 1

    result = successor
    for _ in range(dimension):
        previous = result

        def next_level(start: int, lower: NatFunction = previous) -> int:
            return iterate(lower, envelope(start) + 1, start)

        result = next_level
    return result


def maximal_chain(
    dimension: int, start: int, envelope: NatFunction, node_limit: int = 10000
) -> list[Rank]:
    """Construct an exact-length controlled descending chain.

    The envelope must be nondecreasing.  The explicit node limit is a guard
    for this reference executable, not an ingredient of the theorem.
    """
    if dimension == 0:
        return [()]
    if dimension < 0:
        raise ValueError("The dimension must be a natural number")
    result: list[Rank] = []
    first = envelope(start)
    block_start = start
    for offset in range(first + 1):
        suffixes = maximal_chain(dimension - 1, block_start, envelope, node_limit)
        if len(result) + len(suffixes) > node_limit:
            raise ValueError("Example exceeds the explicit node limit")
        result.extend((first - offset,) + suffix for suffix in suffixes)
        block_start += len(suffixes)
    return result


def verify_chain(chain: list[Rank], start: int, envelope: NatFunction) -> bool:
    if not chain:
        return True
    dimension = len(chain[0])
    return (
        all(len(rank) == dimension for rank in chain)
        and all(
            all(0 <= coordinate <= envelope(start + index) for coordinate in rank)
            for index, rank in enumerate(chain)
        )
        and all(left > right for left, right in zip(chain, chain[1:]))
    )


def reset_step(state: tuple[int, int, int]) -> tuple[int, int, int]:
    a, b, z = state
    if a == 0 and b == 0:
        return state
    if b > 0:
        return a, b - 1, z + 1
    return a - 1, 2**z, z + 1


def active(state: tuple[int, int, int]) -> bool:
    return state[0] + state[1] > 0


def exact_reset_runtime(a: int, b: int, z: int) -> int:
    """The separately proved phase formula, used only for small examples."""
    result = b
    for _ in range(a):
        result = result + 1 + 2 ** (z + result)
    return result


@dataclass
class TrajectoryEnvelope:
    """Finite simulator and running rank maximum; no termination assumption."""

    initial: tuple[int, int, int]
    simulation_limit: int = 10000

    def __post_init__(self) -> None:
        self.states = [self.initial]
        self.maxima = [max(self.initial[:2])]

    def extend(self, time: int) -> None:
        while len(self.states) <= time and active(self.states[-1]):
            if len(self.states) > self.simulation_limit:
                raise ValueError("Example exceeds the finite simulation limit")
            previous = self.states[-1]
            following = reset_step(previous)
            assert previous[:2] > following[:2]
            self.states.append(following)
            self.maxima.append(max(self.maxima[-1], *following[:2]))

    def envelope(self, time: int) -> int:
        self.extend(time)
        return self.maxima[min(time, len(self.maxima) - 1)]

    def state(self, time: int) -> tuple[int, int, int]:
        self.extend(time)
        return self.states[min(time, len(self.states) - 1)]


def validate() -> dict:
    sharp_cases = []
    for constant in range(4):
        for dimension in range(5):
            for start in (0, 2):
                envelope = lambda _, c=constant: c
                fuel = make_fixed_depth_fuel(dimension, envelope)
                chain = maximal_chain(dimension, start, envelope)
                assert verify_chain(chain, start, envelope)
                assert len(chain) == fuel(start) - start == (constant + 1) ** dimension
                sharp_cases.append(
                    {"envelope": f"constant_{constant}", "d": dimension,
                     "s": start, "length": len(chain), "endpoint": fuel(start)}
                )

    envelope = lambda time: time + 1
    increasing_cases = [(0, s) for s in range(5)]
    increasing_cases += [(1, s) for s in range(5)]
    increasing_cases += [(2, s) for s in range(4)]
    increasing_cases += [(3, 0)]
    for dimension, start in increasing_cases:
        fuel = make_fixed_depth_fuel(dimension, envelope)
        chain = maximal_chain(dimension, start, envelope)
        assert verify_chain(chain, start, envelope)
        assert len(chain) == fuel(start) - start
        sharp_cases.append(
            {"envelope": "time_plus_one", "d": dimension, "s": start,
             "length": len(chain), "endpoint": fuel(start)}
        )

    monotonicity_checks = 0
    for constant in range(4):
        for dimension in range(5):
            fuel = make_fixed_depth_fuel(dimension, lambda _, c=constant: c)
            values = [fuel(s) for s in range(8)]
            assert all(value >= s + 1 for s, value in enumerate(values))
            assert all(left <= right for left, right in zip(values, values[1:]))
            monotonicity_checks += 1
    for dimension in range(3):
        fuel = make_fixed_depth_fuel(dimension, lambda time: time + 1)
        values = [fuel(s) for s in range(8)]
        assert all(value >= s + 1 for s, value in enumerate(values))
        assert all(left <= right for left, right in zip(values, values[1:]))
        monotonicity_checks += 1

    reset_cases = []
    for initial in [(0, 0, 0), (0, 5, 7), (1, 0, 0), (1, 3, 1),
                    (2, 0, 0), (2, 1, 0), (2, 0, 1), (3, 0, 0)]:
        simulator = TrajectoryEnvelope(initial)
        bound = make_fixed_depth_fuel(2, simulator.envelope)(0)
        final_state = simulator.state(bound)
        assert not active(final_state)
        halt_time = len(simulator.states) - 1
        assert halt_time == exact_reset_runtime(*initial)
        assert halt_time <= bound
        for time, state in enumerate(simulator.states):
            a0, b0, z0 = initial
            assert state[0] <= a0
            assert state[2] <= z0 + time
            assert state[1] <= b0 + 2 ** (z0 + time)
        reset_cases.append(
            {"initial": list(initial), "exact_halt_time": halt_time,
             "automatic_lex_fuel": bound, "final_state": list(final_state)}
        )

    return {
        "status": "passed",
        "scope": "Finite exact arithmetic examples; not a formal or object-iPRA proof.",
        "standard_library_only": True,
        "maximal_chain_case_count": len(sharp_cases),
        "monotonicity_sample_count": monotonicity_checks,
        "reset_example_count": len(reset_cases),
        "maximal_chain_cases": sharp_cases,
        "reset_examples": reset_cases,
        "large_values_intentionally_not_evaluated": ["F_3(1) with h(t)=t+1"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the validation JSON here")
    args = parser.parse_args()
    result = validate()
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(encoded, encoding="utf-8")
        print(json.dumps({key: result[key] for key in (
            "status", "maximal_chain_case_count", "monotonicity_sample_count",
            "reset_example_count")}, indent=2))
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
