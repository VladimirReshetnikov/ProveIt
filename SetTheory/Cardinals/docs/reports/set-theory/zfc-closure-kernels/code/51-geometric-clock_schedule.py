#!/usr/bin/env python3
"""Replay the actual Cantor-coded command schedule under the two counters.

This checks scheduling and command decoding, not the axiom emitter, the
logical calculus, or a binary tape implementation. Every integer is exact.
The command format is the pinned m254/tools/logic/spec.py and Enum254.lean.
No upstream floating-point or large-number fingerprint implementation is used.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from math import isqrt
from pathlib import Path


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(z: int) -> tuple[int, int]:
    if z < 0:
        raise ValueError("A code must be a natural number")
    diagonal = (isqrt(8 * z + 1) - 1) // 2
    second = z - diagonal * (diagonal + 1) // 2
    return diagonal - second, second


@dataclass(frozen=True)
class Command:
    opcode: int
    x: int
    y: int | None = None
    u: int | None = None

    def numbers(self) -> tuple[int, ...]:
        if self.opcode < 3:
            return self.opcode, self.x
        assert self.y is not None and self.u is not None
        return self.opcode, self.x, self.y, self.u


def decode(query: int) -> tuple[int, Command]:
    ac, remaining = unpair(query)
    x, remaining = unpair(remaining)
    if ac < 3:
        return remaining, Command(ac, x)
    y, remaining = unpair(remaining)
    u, remaining = unpair(remaining)
    return remaining, Command(ac, x, y, u)


def encode(command: Command, remaining: int) -> int:
    result = remaining
    for component in reversed(command.numbers()):
        result = pair(component, result)
    return result


def legacy_step(next_candidate: int, remaining: int):
    if remaining == 0:
        query = next_candidate
        next_candidate += 1
    else:
        query = remaining - 1
    tail, command = decode(query)
    return next_candidate, tail, query, command


def geometric_step(gap: int, remaining: int):
    query = gap if remaining == 0 else remaining - 1
    tail, command = decode(query)
    return gap + int(tail == 0), tail, query, command


def run_check(first: int, candidates: int) -> dict:
    """Compare two independently stored scheduler states at every command."""
    next_candidate, old_remaining = first, 0
    gap, new_remaining = first, 0
    trace_hash = hashlib.sha256()
    total_commands = 0
    max_commands = 0
    current_commands = 0
    boundaries = 0
    examples = []
    last_gap = gap
    while boundaries < candidates:
        old = legacy_step(next_candidate, old_remaining)
        new = geometric_step(gap, new_remaining)
        assert old[2:] == new[2:], (old, new)
        next_candidate, old_remaining = old[:2]
        gap, new_remaining = new[:2]
        assert old_remaining == new_remaining
        assert next_candidate == gap + int(new_remaining != 0)
        query, command = old[2:]
        tail = old_remaining
        assert encode(command, tail) == query
        assert tail <= query
        if current_commands:
            assert tail < before_tail
        before_tail = tail
        trace_hash.update((str(query) + ":" + ",".join(map(str, command.numbers()))
                           + ":" + str(tail) + "\n").encode())
        total_commands += 1
        current_commands += 1
        if tail == 0:
            assert gap == last_gap + 1
            assert current_commands <= last_gap + 1
            max_commands = max(max_commands, current_commands)
            if len(examples) < 12:
                examples.append({"candidate": last_gap, "commands": current_commands,
                                 "gap_after": gap})
            boundaries += 1
            last_gap = gap
            current_commands = 0
        else:
            assert gap == last_gap
    return {"first_candidate": first, "candidates_completed": boundaries,
            "last_candidate": gap - 1, "command_steps": total_commands,
            "max_commands_in_one_candidate": max_commands,
            "trace_sha256": trace_hash.hexdigest(), "examples": examples,
            "every_command_agrees": True,
            "candidate_gaps_exactly_one": True,
            "scope": "Exact command-code schedule; no formula execution or TM run"}


def local_refinement_check() -> dict:
    # These independent finite cases also exercise possible halting bodies;
    # the universal result is proved in GapClock.lean, not inferred from them.
    cases = 0
    for g in range(8):
        for old_tail in range(8):
            observed_next = g + int(old_tail != 0)
            query_old = observed_next if old_tail == 0 else old_tail - 1
            query_new = g if old_tail == 0 else old_tail - 1
            assert query_old == query_new
            for returned_tail in [None, *range(8)]:
                if returned_tail is None:
                    old_out = new_out = None
                else:
                    old_np = observed_next + int(old_tail == 0)
                    new_gap = g + int(returned_tail == 0)
                    old_out = old_np, returned_tail
                    new_out = new_gap + int(returned_tail != 0), returned_tail
                assert old_out == new_out
                cases += 1
    # Deliberately incrementing the gap after every command is not a refinement.
    g, returned_tail = 40, 40
    expected_next = g + 1
    incorrect_next = (g + 1) + int(returned_tail != 0)
    assert expected_next != incorrect_next
    return {"finite_local_cases": cases,
            "per_command_clock_mutation_rejected": True,
            "mutation_witness": {"initial_gap": g, "returned_tail": returned_tail,
                                 "expected_virtual_next": expected_next,
                                 "incorrect_virtual_next": incorrect_next}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidates", type=int, default=100000)
    parser.add_argument("--output", type=Path, default=Path("clock_schedule_results.json"))
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions must be enabled")
    if args.candidates < 1:
        parser.error("Positive candidate count required")
    result = {"status": "PASS", "local": local_refinement_check(),
              "runs": [run_check(seed, args.candidates) for seed in [0, 40, 137]],
              "proof_file": "GapClock.lean", "binary_implementation": "not supplied",
              "source": {"repository": "VladimirReshetnikov/ProveIt",
                         "commit": "85633fd2f57b5dca16f87667699134d1b500ebc0",
                         "paths": ["lib/jeff-busy-beaver-zfc254/ZF/m254/tools/logic/spec.py",
                                   "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean"]}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"],
                      "local_cases": result["local"]["finite_local_cases"],
                      "candidates": sum(r["candidates_completed"] for r in result["runs"]),
                      "commands": sum(r["command_steps"] for r in result["runs"])}))


if __name__ == "__main__":
    main()
