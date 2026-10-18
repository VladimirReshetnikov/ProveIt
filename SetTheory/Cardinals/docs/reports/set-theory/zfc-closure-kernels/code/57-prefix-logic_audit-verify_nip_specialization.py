#!/usr/bin/env python3
"""Check the proposed constant-one NIP comparison on exact register values.

The old branch follows the literal increment-X, destructive equality, and
pop contracts. The new branch uses two conditional H decrements. This is
not a binary-table or source-DAG control-level verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from verify_source_rewrite import W, pair, unpair


def old_nip(w: W) -> W | None:
    x = 1  # Original increment of initially zero scratch1.
    h = w.h
    # Exact joint decrement loop124: X ends zero, H is |old_X-old_H|.
    while x:
        x -= 1
        if h:
            h -= 1
        else:
            h += x + 1
            x = 0
    if not h:
        return None
    # The unequal branch consumes its test decrement and clears H.
    h -= 1
    while h:
        h -= 1
    top, tail = unpair(w.s)
    return W(w.t, tail, w.d, h + top)


def new_nip(w: W) -> W | None:
    h = w.h
    if h:
        h -= 1
        if not h:
            return None
        h -= 1
        while h:
            h -= 1
    top, tail = unpair(w.s)
    return W(w.t, tail, w.d, h + top)


def verify() -> dict:
    count = halted = 0
    for t in [0, 1, 2, 11]:
        for d in [0, 1, 7]:
            for h in list(range(17)) + [31, 127, 1024]:
                for top, tail in [(0, 0), (1, 0), (0, 9), (2, 7), (23, 31)]:
                    w = W(t, pair(top, tail), d, h)
                    expected = None if h == 1 else W(t, tail, d, top)
                    assert old_nip(w) == expected
                    assert new_nip(w) == expected
                    count += 1
                    halted += h == 1
    return {
        "status": "passed",
        "exact_cases": count,
        "halting_cases": halted,
        "source_scratch_precondition": "X=Y=0",
        "nonhalting_result": "T and D preserved; H=first(S); S=second(S); X=Y=0",
        "binary_table_verified": False,
        "dag_control_levels_verified": False,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
