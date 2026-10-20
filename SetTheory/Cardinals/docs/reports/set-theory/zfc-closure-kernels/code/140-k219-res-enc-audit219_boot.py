#!/usr/bin/env python3
"""Independent dense two-half-tape audit of the selected native 219 prefix."""
from pathlib import Path
import argparse
import hashlib
import json

PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SEED = [3, 0, 0, 0, 3, 0, 0, 0, 0]
TABLE_SHA = "b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("table", type=Path)
    ap.add_argument("output", type=Path)
    args = ap.parse_args()
    raw = args.table.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == TABLE_SHA
    table = {}
    for line in raw.decode("ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, n = line.split()
        key = int(q), int(b)
        assert key not in table and d in ("L", "R")
        table[key] = (int(w), -1 if d == "L" else 1, int(n))
    working = {q for q, _ in table}
    assert len(working) == 219 and len(table) == 438
    assert all((q, b) in table for q in working for b in (0, 1))
    assert {n for _, _, n in table.values()} - working == {254}

    # Two independent byte arrays indexed by h and -h-1, rather than the
    # sparse dictionary/set representation used by the construction scripts.
    nonnegative, negative = bytearray(1), bytearray()
    q = h = 0
    used = set()
    steps = 312617
    for _ in range(steps):
        buf, offset = (nonnegative, h) if h >= 0 else (negative, -h - 1)
        if offset >= len(buf):
            buf.extend(bytes(offset + 1 - len(buf)))
        b = buf[offset]
        used.add((q, b))
        w, direction, q = table[q, b]
        buf[offset] = w
        h += direction
        assert q != 254
    assert q == 84
    ones = {i for i, b in enumerate(nonnegative) if b}
    ones.update(-i - 1 for i, b in enumerate(negative) if b)
    assert h - 1 in ones
    header = min(x for x in ones if x >= h + 64)
    gap = header - h - 64
    assert {x for x in ones if x < header} == {h - 1}

    values = []
    p = header + 1
    last = max(ones)
    while p <= last:
        assert p not in ones and p + 1 in ones
        p += 1
        start = p
        while p in ones:
            p += 1
        values.append(p - start - 1)
    assert p == last + 1 and len(values) >= 10
    physical, spares = values[:9], values[9:]
    logical = [physical[j] for j in PHY]
    assert logical == SEED and gap == 80 and spares == [1] * 130

    # Reconstruct and compare the whole support, including zero exterior.
    reconstructed = {h - 1, h + 64 + gap}
    p = h + 64 + gap + 1
    for value in physical + spares:
        p += 1
        reconstructed.update(range(p, p + value + 1))
        p += value + 1
    assert reconstructed == ones
    report = {"status": "INDEPENDENT_COMPLETE_BLANK_PREFIX_PASS",
              "table_sha256": TABLE_SHA, "working_states": 219,
              "transition_rows": 438, "steps": steps, "state": q,
              "head": h, "header": header, "gap": gap,
              "logical_registers": logical, "physical_registers": physical,
              "spares": spares, "one_cells": sorted(ones),
              "one_count": len(ones), "all_other_cells": 0,
              "used_rows": sorted(used),
              "scope": "Complete finite blank prefix only; runtime/calibration separate"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("one_cells", "spares", "used_rows")}, indent=2))


if __name__ == "__main__":
    main()
