#!/usr/bin/env python3
"""Reconstruct the exact 253-state candidate from the accepted ZFC254 table.

The 254-state baseline was designed and built by Mira-Cult; its notice and
provenance are retained in ZF/m254/README.md. This local reduction changes four
rows, deletes old state 8, and applies the explicit bijection below. No search,
external archive, network access, or exploratory metadata is needed.

Default/--check verifies the committed file; --write explicitly regenerates it.
"""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("Run with assertions enabled, not python -O")

HERE = Path(__file__).resolve().parent.parent
BASELINE = HERE.parent / "m254" / "machine" / "zfc_254.tm"
MACHINE = HERE / "machine" / "zfc_253.tm"
BASE_SHA256 = "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"
CANDIDATE_SHA256 = "84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95"

# Compact label -> old label, including the terminal as the final entry.
# This is the frozen bijection of the accepted experimental table. Old 5 is
# the shared startup/helper state; old 8 is deleted; old 254 remains terminal.
OLD_OF = (
    5, 97, 64, 112, 85, 28, 131, 40, 63, 38, 48, 56, 7, 31, 10, 44,
    14, 60, 20, 0, 2, 1, 4, 3, 6, 9, 13, 19, 29, 41, 58, 74,
    84, 96, 110, 111, 33, 128, 129, 130, 47, 148, 12, 121, 149, 107, 150, 27,
    18, 167, 17, 144, 145, 25, 170, 125, 171, 172, 32, 39, 92, 26, 82, 71,
    30, 201, 147, 21, 202, 203, 204, 45, 46, 57, 24, 93, 94, 34, 42, 43,
    169, 11, 175, 88, 113, 61, 62, 73, 36, 37, 108, 50, 49, 59, 15, 16,
    105, 102, 103, 23, 132, 76, 77, 78, 83, 53, 54, 55, 126, 127, 75, 22,
    123, 124, 119, 120, 35, 151, 86, 87, 89, 95, 69, 70, 72, 81, 68, 67,
    146, 141, 142, 143, 51, 52, 173, 98, 99, 100, 101, 104, 109, 65, 79, 80,
    168, 166, 66, 114, 115, 116, 117, 118, 122, 90, 91, 200, 133, 134, 135, 136,
    137, 138, 139, 140, 106, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162,
    163, 164, 165, 174, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
    188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 205, 206, 207, 208,
    209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
    225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240,
    241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
)
OLD_TO_COMPACT = {old: compact for compact, old in enumerate(OLD_OF)}
DELTA = {
    (3, 0): (0, "L", 48),
    (5, 0): (1, "R", 97),
    (5, 1): (1, "R", 64),
    (49, 1): (0, "R", 5),
}


def parse_table(data: bytes):
    rows, start = {}, None
    for line in data.decode("utf-8").splitlines():
        if line.startswith("#! start "):
            assert start is None, "duplicate start declaration"
            start = int(line[len("#! start "):])
        elif line and not line.startswith("#"):
            q, bit, write, direction, target = line.split()
            key = int(q), int(bit)
            row = int(write), direction, int(target)
            assert key not in rows and key[1] in (0, 1)
            assert row[0] in (0, 1) and direction in ("L", "R")
            rows[key] = row
    assert start is not None
    return start, rows


def patched_rows(baseline: Path = BASELINE):
    data = baseline.read_bytes()
    assert hashlib.sha256(data).hexdigest() == BASE_SHA256, "baseline SHA256 mismatch"
    start, original = parse_table(data)
    assert start == 0
    assert set(original) == {(q, bit) for q in range(254) for bit in (0, 1)}
    assert len(OLD_OF) == len(OLD_TO_COMPACT) == 254
    assert set(OLD_OF) == set(range(255)) - {8}
    assert OLD_OF[0] == 5 and OLD_OF[33] == 96 and OLD_OF[253] == 254
    assert all(original[key] != row for key, row in DELTA.items())
    result = {key: DELTA.get(key, row) for key, row in original.items() if key[0] != 8}
    assert {key for key, row in result.items() if row != original[key]} == set(DELTA)
    assert len(result) == 506 and all(target != 8 for _, _, target in result.values())
    return result


def candidate_rows(baseline: Path = BASELINE):
    rows = {(OLD_TO_COMPACT[q], bit): (write, direction, OLD_TO_COMPACT[target])
            for (q, bit), (write, direction, target) in patched_rows(baseline).items()}
    assert set(rows) == {(q, bit) for q in range(253) for bit in (0, 1)}
    assert all(0 <= target <= 253 for _, _, target in rows.values())
    reachable, todo = {0}, deque([0])
    while todo:
        q = todo.popleft()
        if q == 253:
            continue
        for bit in (0, 1):
            target = rows[q, bit][2]
            if target not in reachable:
                reachable.add(target)
                todo.append(target)
    assert reachable == set(range(254)), "every counted state must be graph reachable"
    return rows


def generate_candidate(baseline: Path = BASELINE) -> bytes:
    rows = candidate_rows(baseline)
    data = ("#! start 0\n" + "".join(
        f"{q} {bit} {write} {direction} {target}\n"
        for (q, bit), (write, direction, target) in
        sorted(rows.items(), key=lambda entry: (str(entry[0][0]), entry[0][1])))).encode("ascii")
    assert hashlib.sha256(data).hexdigest() == CANDIDATE_SHA256, "generated candidate SHA256 mismatch"
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true")
    group.add_argument("--write", action="store_true")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    parser.add_argument("--output", type=Path, default=MACHINE)
    parser.add_argument("--print-map", action="store_true")
    args = parser.parse_args()
    data = generate_candidate(args.baseline)
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(data)
    else:
        assert args.output.read_bytes() == data, "literal machine differs from exact generated candidate"
    if args.print_map:
        print(json.dumps(OLD_TO_COMPACT, sort_keys=True))
    else:
        print(f"zfc_253.tm: exact four-row delta, deleted old8, explicit bijection, 253 working states; SHA256 {CANDIDATE_SHA256}")


if __name__ == "__main__":
    main()
