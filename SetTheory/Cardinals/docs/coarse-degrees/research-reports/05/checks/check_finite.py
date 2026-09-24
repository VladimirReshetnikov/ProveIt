#!/usr/bin/env python3
"""Deterministic finite checks for the accompanying conventional proof.

These checks do not verify Turing noncomputability, density convergence,
perfectness, or the infinite minimal-pair theorem. The reservoir test is
only a finite, single-input model of the cross-disagreement argument.

Run from any working directory with Python 3.9+:
    python checks/check_finite.py --output checks/results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set

from enumerate_witness import (
    approximate_witness, column_coordinates, column_position,
    decode_instruction, decode_list, decode_program, encode_instruction,
    encode_list, encode_program, finite_column_ones, pair, run_program, unpair,
)


def require(condition: bool, message: str) -> None:
    # Unlike assert, these checks cannot be disabled by python -O.
    if not condition:
        raise AssertionError(message)


def check_coding() -> Dict[str, int]:
    pairing_tests = 0
    for a in range(64):
        for b in range(64):
            require(unpair(pair(a, b)) == (a, b), "pairing round trip")
            pairing_tests += 1
    list_tests = 0
    for length in range(5):
        for values in itertools.product(range(4), repeat=length):
            require(decode_list(encode_list(values)) == list(values),
                    "list round trip")
            list_tests += 1
    for code in range(4096):
        require(encode_list(decode_list(code)) == code, "code round trip")
        require(encode_instruction(decode_instruction(code)) == code,
                "instruction round trip")
    program_tests = 0
    programs = [
        ((0,),),  # Identity.
        ((1, 0, 1), (0,)),  # Successor.
        ((2, 0, 1, 0), (0,)),  # Zero.
        ((2, 0, 1, 0), (1, 0, 2), (0,)),  # Constant one.
    ]
    for program in programs:
        require(decode_program(encode_program(program)) == program,
                "program round trip")
    for n in range(64):
        expected = [n, n + 1, 0, 1]
        for program, value in zip(programs, expected):
            require(run_program(program, n, 128) == value, "machine output")
            program_tests += 1
    require(run_program(((1, 0, 0),), 0, 128) is None, "loop stays unknown")
    require(run_program((), 0, 128) is None, "empty program does not halt")
    require(run_program(((0,),), 0, 0) is None, "zero budget is unknown")
    return {"pairing_round_trips": pairing_tests,
            "list_round_trips": list_tests,
            "code_and_instruction_round_trips": 4096,
            "machine_outputs": program_tests,
            "unknown_status_tests": 3}


def check_dyadic() -> Dict[str, int]:
    counts = [0] * 13
    count_tests = 0
    for n in range(4096):
        e, j = column_coordinates(n)
        require(column_position(e, j) == n, "column inverse")
        for k in range(13):
            # Independent direct count, compared with the closed formula.
            if e >= k:
                counts[k] += 1
            require(counts[k] == (n + 1) // (1 << k), "dyadic tail count")
            count_tests += 1
    return {"column_inverse_tests": 4096, "tail_count_tests": count_tests}


def check_column_stopping() -> Dict[str, int]:
    alphabet: Sequence[Optional[int]] = (None, 0, 1, 2)
    trace_tests = 0
    refinement_tests = 0
    for trace in itertools.product(alphabet, repeat=5):
        got = finite_column_ones(trace)
        expected = {
            j for j, value in enumerate(trace)
            if value == 0 and all(v in (0, 1) for v in trace[:j + 1])
        }
        require(got == expected, "finite column formula")
        trace_tests += 1
        for i, value in enumerate(trace):
            if value is None:
                for new_value in (0, 1, 2):
                    refined = list(trace)
                    refined[i] = new_value
                    require(got <= finite_column_ones(refined),
                            "new convergence must not retract enumerated ones")
                    refinement_tests += 1
    stages = [0, 1, 2, 8, 16, 32, 64, 128, 256, 512, 1024]
    previous: Set[int] = set()
    sizes: List[int] = []
    for stage in stages:
        current = set(approximate_witness(stage).ones)
        require(previous <= current, "stage approximation is monotone")
        require(all(0 <= n < stage for n in current), "stage support bound")
        previous = current
        sizes.append(len(current))
    return {"column_trace_tests": trace_tests,
            "convergence_refinement_tests": refinement_tests,
            "monotone_stage_tests": len(stages),
            "final_stage": stages[-1], "final_one_count": sizes[-1]}


def check_product_lemma() -> Dict[str, int]:
    tables = list(itertools.product((None, 0, 1, 2), repeat=4))
    all_masks = range(1, 1 << 4)
    pairs = 0
    disagreements = 0
    no_conflict = 0
    restriction_tests = 0
    for left in tables:
        left_outputs = {v for v in left if v is not None}
        for right in tables:
            right_outputs = {v for v in right if v is not None}
            pairs += 1
            conflict = any(a != b for a in left_outputs for b in right_outputs)
            if conflict:
                disagreements += 1
                continue
            no_conflict += 1
            if left_outputs and right_outputs:
                require(len(left_outputs | right_outputs) == 1,
                        "without cross conflict, both sides must agree")
                first_left = next(v for v in left if v is not None)
                require(all(first_left == v for v in right_outputs),
                        "first convergence computes any common output")
            # Shrinking either reservoir cannot create a cross conflict.
            for mask in all_masks:
                restricted_left = {left[i] for i in range(4)
                                   if mask & (1 << i) and left[i] is not None}
                require(not any(a != b for a in restricted_left
                                for b in right_outputs), "left persistence")
                restricted_right = {right[i] for i in range(4)
                                    if mask & (1 << i) and right[i] is not None}
                require(not any(a != b for a in left_outputs
                                for b in restricted_right), "right persistence")
                restriction_tests += 2
    return {"table_pairs": pairs, "cross_disagreements": disagreements,
            "no_cross_disagreement_pairs": no_conflict,
            "reservoir_restriction_tests": restriction_tests}


def check_density_budget() -> Dict[str, int]:
    tests = 0
    for n in range(1, 257):
        for k in range(9):
            q = {x for x in range(n) if (x + 1) % (1 << k) == 0}
            for length in (0, 1, 3, 8, 31, 64, 256):
                worst_error_set = set(range(min(length, n))) | q
                require(len(worst_error_set) <= length + n // (1 << k),
                        "finite density budget")
                tests += 1
    blocks = 0
    for k in range(9):
        start = 1 << (1 << k)
        end = 1 << (1 << (k + 1))
        require(Fraction(end - start, 2 * end) >= Fraction(1, 4),
                "incorrect majority causes large prefix error")
        blocks += 1
    return {"density_budget_tests": tests, "block_ratio_tests": blocks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results: Dict[str, Any] = {
        "status": "passed",
        "python": platform.python_version(),
        "deterministic": True,
        "coding": check_coding(),
        "dyadic_partition": check_dyadic(),
        "column_stopping": check_column_stopping(),
        "finite_product_lemma": check_product_lemma(),
        "density_estimates": check_density_budget(),
        "not_verified": [
            "Turing noncomputability or non-coarse-computability",
            "infinite density convergence",
            "existence or perfectness of the infinite branch family",
            "Turing minimal pairs or the prescribed-infimum theorem",
            "a Lean/kernel formalization or literature novelty",
        ],
    }
    text = json.dumps(results, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
