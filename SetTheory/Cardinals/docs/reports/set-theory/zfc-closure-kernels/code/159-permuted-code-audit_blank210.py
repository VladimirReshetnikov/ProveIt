#!/usr/bin/env python3
"""Independently replay the exact 216-state candidate's complete blank prefix.

Usage: python audit_blank210.py TABLE STARTUP_JSON OUTPUT_JSON

This audit uses its own table parser and a dense tape.  It compares every
transition against the separately generated sparse-simulator trace, then
compares the whole tape against a direct construction of the stated seed.
It does not prove the unbounded runtime contract or the logical calibration.
Only the Python standard library is required.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


EXPECTED_TABLE_SHA256 = "eff4f5a3e2c81a674d1a799f634ee4606708b79899e65e8c3cb688dc87c954a3"
STEPS = 95674


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path)
    parser.add_argument("startup_json", type=Path)
    parser.add_argument("output_json", type=Path)
    args = parser.parse_args()
    require(sha(args.table) == EXPECTED_TABLE_SHA256, "Unexpected native-table bytes")

    table = {}
    for line_number, line in enumerate(args.table.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        require(len(fields) == 5, f"Malformed table line {line_number}")
        q, bit, write, direction, target = fields
        q, bit, write, target = map(int, (q, bit, write, target))
        require((q, bit) not in table, f"Duplicate row on line {line_number}")
        require(bit in (0, 1) and write in (0, 1), "Nonbinary row")
        require(direction in ("L", "R"), "Invalid movement")
        table[q, bit] = (write, -1 if direction == "L" else 1, target)

    states = {q for q, bit in table}
    require(len(states) == 216 and len(table) == 432, "Wrong state or row count")
    require(254 not in states, "Halt label has outgoing rows")
    require(all((q, bit) in table for q in states for bit in (0, 1)),
            "Transition function is not total on working states")
    require({target for write, direction, target in table.values()} - states == {254},
            "Unexpected external transition target")

    receipt = json.loads(args.startup_json.read_text())
    require(receipt["steps"] == STEPS, "Wrong recorded prefix length")
    require(len(receipt["trace"]) == STEPS, "Wrong trace length")

    # Every dense-tape access is explicitly checked before use.  The recorded
    # visited interval below is much smaller than the chosen finite buffer.
    tape = bytearray(200001)
    origin = 100000
    q, head = 0, origin
    lowest = highest = head
    for tick in range(STEPS):
        require(0 <= head < len(tape), "Dense-tape boundary reached")
        bit = tape[head]
        require((q, bit) in table, f"Premature halt or undefined row at step {tick}")
        write, direction, target = table[q, bit]
        require(receipt["trace"][tick] ==
                [q, head - origin, bit, write, direction, target],
                f"Sparse/dense trace mismatch at step {tick}")
        tape[head] = write
        head += direction
        q = target
        lowest, highest = min(lowest, head), max(highest, head)

    ones = [i - origin for i, bit in enumerate(tape) if bit]
    require(q == 84 and head - origin == -8, "Wrong final control configuration")

    # Directly construct the complete expected tape without importing either
    # runtime checker or its frame-construction helper.
    logical = [4, 0, 0, 0, 0, 0, 0, 0, 0]
    spares = [1] * 40
    physical = [0] * 9
    for logical_index, physical_index in enumerate((6, 2, 0, 4, 3, 7, 8, 5, 1)):
        physical[physical_index] = logical[logical_index]
    final_head = -8
    header = final_head + 65
    expected = {final_head - 1, header}
    position = header + 1
    for value in physical + spares:
        require(position not in expected, "Frame delimiter collision")
        expected.update(range(position + 1, position + value + 2))
        position += value + 2
    require(ones == sorted(expected), "Whole tape differs from the required frame")
    require(ones == receipt["one_cells"], "Whole tape differs from sparse receipt")
    require(receipt["registers"] == logical and receipt["spares"] == spares,
            "Wrong logical values in sparse receipt")
    require(receipt["gap"] == 1 and receipt["state"] == 84 and receipt["head"] == -8,
            "Wrong physical metadata in sparse receipt")

    output = {
        "status": "PASS",
        "table_sha256": sha(args.table),
        "startup_receipt_sha256": sha(args.startup_json),
        "auditor_sha256": sha(Path(__file__)),
        "working_states": 216,
        "rows": 432,
        "sole_external_halt": 254,
        "initial_state": 0,
        "blank_steps": STEPS,
        "final_state": 84,
        "final_head": -8,
        "visited_head_interval": [lowest - origin, highest - origin],
        "whole_tape_one_cells": ones,
        "header_distance": 65,
        "gap_extra": 1,
        "logical_registers": logical,
        "spares": spares,
        "trace_equal_to_separate_sparse_simulator": True,
        "whole_tape_equal_to_direct_frame_construction": True,
        "scope": "Finite blank prefix and exact whole-tape endpoint only.",
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: v for k, v in output.items()
                      if k not in ("whole_tape_one_cells", "spares")}, indent=2))


if __name__ == "__main__":
    main()
