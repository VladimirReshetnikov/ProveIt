#!/usr/bin/env python3
"""Independent finite audit: compute UNTRUNCATED Grundy values by bit masks.

This does not import verify.py or use its gap-window recurrence. Membership is
computed afresh from generators. Every certificate entry is compared with a
literal finite-poset game-tree calculation. This audits the finite computation;
the infinite conclusion additionally uses the proof of the window recurrence.
"""
from __future__ import annotations
import csv
import json
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def audit(path: Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    generators = data["generators"]
    end = data["row_end"] + max(data["gaps"])
    membership = [False] * (end + 1)
    membership[0] = True
    for n in range(1, end + 1):
        membership[n] = any(n >= a and membership[n-a] for a in generators)
    values = [n for n in range(end + 1) if membership[n]]
    index = {n: i for i, n in enumerate(values)}
    upper = [sum(1 << j for j, z in enumerate(values)
                 if z >= y and membership[z-y]) for y in values]

    @lru_cache(maxsize=None)
    def grundy(mask: int) -> int:
        options = set()
        remaining = mask
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            i = bit.bit_length() - 1
            options.add(grundy(mask & ~upper[i]))
        result = 0
        while result in options:
            result += 1
        return result

    def pack(position) -> int:
        return sum(1 << index[n] for n in position)

    output = []
    for offset, encoded in enumerate(data["rows"]):
        x = data["row_start"] + offset
        prefix = [n for n in values if n < x]
        for column, shape in enumerate(data["pattern_masks"]):
            tail = [x+g for i, g in enumerate(data["gaps"]) if shape >> i & 1]
            exact = grundy(pack(prefix + tail))
            if min(exact, 3) != int(encoded[column]):
                raise ValueError(f"Finite audit mismatch: x={x}, mask={shape}")
            output.append((x, shape, exact, min(exact, 3)))
    for b in range(1, data["row_start"]):
        if membership[b]:
            remainder = [n for n in values if n < b or not membership[n-b]]
            exact = grundy(pack(remainder))
            if exact < 3:
                raise ValueError(f"Exceptional low Apéry value at {b}")
    diamond_value = grundy(pack(data["apery_four"]))
    if diamond_value != 3:
        raise ValueError("The four-point diamond has an incorrect value.")
    csv_path = ROOT / "data" / (path.stem + "_exact_finite_audit.csv")
    with csv_path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["x", "shape_mask", "exact_grundy", "capped_grundy"])
        writer.writerows(output)
    print(f"PASS independent audit {tuple(generators)}: "
          f"{len(output)} exact finite-position values checked")
    print(f"  {grundy.cache_info().currsize} distinct finite positions evaluated")
    print(f"  Exact diamond value: {diamond_value}")


if __name__ == "__main__":
    for certificate in sorted((ROOT / "certificates").glob("s4[0-9][0-9].json")):
        audit(certificate)
    print("ALL INDEPENDENT FINITE AUDITS PASSED.")
