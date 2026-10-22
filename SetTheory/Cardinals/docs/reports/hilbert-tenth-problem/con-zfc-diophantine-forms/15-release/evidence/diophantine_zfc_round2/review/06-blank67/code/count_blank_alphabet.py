#!/usr/bin/env python3
"""Exact cardinality of the lifted K215 blank-helical alphabet.

Count by a closed category formula and independently by the actual finite
local predicate on every left/right pair for representative center types.
The four diagonal corners are unconstrained and contribute 439**4.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from verify_k215 import parse_tm, require
import blank_helical as b


def direct_center_count(center, table):
    v, h, payload, phase = b.DECODED[center]
    predecessor, predecessor_count = (0, 439) if v or h else (b.H, 1) if phase else (0, 438)
    total = 0
    window = [0]*9
    window[1] = predecessor
    window[4] = center
    for left in range(439):
        window[3] = left
        lt = b.DECODED[left]
        for right in range(439):
            window[5] = right
            rt = b.DECODED[right]
            candidates = [(b.V, 1)] if v else [(0, 437)] if h else [(b.H, 1)]
            if not v and not h and (lt[0] or lt[2] is not None) and (rt[0] or rt[2] is not None):
                expected = b.next_payload((0, None) if lt[0] else lt[2], payload,
                                          (0, None) if rt[0] else rt[2], table)
                if expected is not None:
                    symbol, state = expected
                    candidates.append((b.normal(symbol, state), 1))
                    if expected == (0, None):
                        candidates += [(b.L, 1), (b.R, 1)]
                    elif expected == (0, 0):
                        candidates.append((b.Q, 1))
            for following, weight in candidates:
                window[7] = following
                if b.local_valid(window, table):
                    total += predecessor_count*weight
    return total


def verify(rows, direct=True):
    table = b.table_from_rows(rows)
    li = sum(d == 1 for _, _, _, d, _ in rows)+1  # Q has the same outgoing head as 0/0.
    ri = sum(d == -1 for _, _, _, d, _ in rows)
    l0 = sum(d == 1 and n == 0 for _, _, _, d, n in rows)
    r0 = sum(d == -1 and n == 0 for _, _, _, d, n in rows)
    ln, rn = 438-li, 438-ri
    boundary_output = 439*438
    categories = []

    def add(name, center, multiplicity, each):
        actual = direct_center_count(center, table) if direct else None
        require(not direct or actual == each, f"Direct count disagrees for {name}: {actual} != {each}")
        categories.append({"name": name, "representative_code": center,
                           "center_multiplicity": multiplicity, "crosses_per_center": each,
                           "direct_crosses_per_center": actual, "crosses": multiplicity*each})

    add("V", b.V, 1, 438*439**2)
    add("H", b.H, 1, 2*437*439**2)
    for symbol in (0, 1):
        internal = ln*rn+li*rn+ri*ln
        if symbol == 0:
            internal += 2*ln*rn+l0*rn+r0*ln
        add(f"headless-{symbol}", b.normal(symbol), 1, 438*(boundary_output+internal))
        add(f"halt-{symbol}", b.normal(symbol, 215), 1, 438*(boundary_output+ln*rn))
    for write in (0, 1):
        for direction in (-1, 1):
            actions = [row for row in rows if row[2] == write and row[3] == direction]
            require(actions, "Missing center type")
            l, r = ln-(direction == -1), rn-(direction == 1)
            internal = l*r+li*r+ri*l
            if write == 0:
                internal += 2*l*r+l0*r+r0*l
            q, symbol, *_ = actions[0]
            add(f"nonhalt-write{write}-move{direction}", b.normal(symbol, q), len(actions), 438*internal)
    add("initial-L", b.L, 1, 2*439+2*(3*ln+li+l0))
    add("initial-Q", b.Q, 1, 437)
    add("initial-R", b.R, 1, 2*438+2*(3*(ln-1)+li+l0))
    require(sum(c["center_multiplicity"] for c in categories) == 439, "Center partition is incomplete")
    cross = sum(c["crosses"] for c in categories)
    return {"schema": "proveit-k215-blank-alphabet-cardinality-v1",
            "left_incoming_right": li, "right_incoming_left": ri,
            "left_nonincoming": ln, "right_nonincoming": rn,
            "left_incoming_target0": l0, "right_incoming_target0": r0,
            "categories": categories,
            "valid_crosses": cross, "free_corner_factor": 439**4,
            "lifted_alphabet_cardinality": cross*439**4,
            "all_raw_windows": 439**9,
            "independent_direct_predicate_enumeration": direct}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tm", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--formula-only", action="store_true")
    args = parser.parse_args()
    result = verify(parse_tm(args.tm.read_bytes()), not args.formula_only)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

