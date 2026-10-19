#!/usr/bin/env python3
"""Check the local slowdown formula and the canonical machine's full boot."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Assertions are required.")
ROOT = Path(__file__).resolve().parents[1]


def read(path):
    result = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith("#"):
            q, b, w, d, t = line.split()
            result[int(q), int(b)] = int(w), (1 if d == "R" else -1), int(t)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    old_path = args.root / "reference/zfc240_old.tm"
    new_path = args.root / "machines/zfc239.tm"
    assert sha256(old_path.read_bytes()).hexdigest() == "547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f"
    assert sha256(new_path.read_bytes()).hexdigest() == "4447a2423907f2b96e8bcd6c88ed2d1e353f925fb8cf36ca913224ddce5914ba"
    old, new = read(old_path), read(new_path)
    expected, position = {-6, 176}, 177
    physical = [0, 0, 0, 3, 0, 0, 3, 0, 0]
    for value in physical + [1] * 167:
        position += 1
        expected.update(range(position, position + value + 1))
        position += value + 1
    tape, state, head, counts = set(), 95, 0, Counter()
    for _ in range(409691):
        bit = int(head in tape)
        counts[state, bit] += 1
        if state == 169 and bit == 1:
            assert head + 1 in tape
        write, move, state = old[state, bit]
        (tape.add if write else tape.discard)(head)
        head += move
    assert (state, head, tape) == (96, -5, expected)
    keys = ((80, 0), (169, 0), (169, 1), (91, 1))
    assert [counts[k] for k in keys] == [18, 12, 6, 3]
    extra = sum(coefficient * counts[k] for coefficient, k in zip((4, 2, 4, 8), keys))
    assert extra == 144
    clock = 409691 + extra
    # Different storage and canonical labels from the sparse old-table loop.
    offset = 2048
    cells = bytearray(4096)
    rules = [[new[q, b] for b in (0, 1)] for q in range(239)]
    state, position = 0, offset
    for _ in range(clock):
        assert state < 239 and 0 <= position < len(cells)
        write, move, state = rules[state][cells[position]]
        cells[position] = write
        position += move
    assert (state, position - offset) == (84, -5)
    assert {i - offset for i, value in enumerate(cells) if value} == expected
    result = {
        "status": "EXACT_239_CANONICAL_BOOT_AND_CLOCK_PASS",
        "baseline_steps": 409691, "candidate_steps": clock, "extra_steps": extra,
        "old_exceptional_visits": {f"{q}/{b}": counts[q, b] for q, b in keys},
        "extra_coefficients": [4, 2, 4, 8],
        "canonical_state": 84, "head": -5, "marker": -6, "header": 176,
        "primary_physical_values": physical, "spare_blocks": 167, "spare_values": 1,
        "one_positions": sorted(expected), "zero_exterior": True,
        "whole_tape_equality": True,
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "one_positions"}, indent=2))


if __name__ == "__main__":
    main()
