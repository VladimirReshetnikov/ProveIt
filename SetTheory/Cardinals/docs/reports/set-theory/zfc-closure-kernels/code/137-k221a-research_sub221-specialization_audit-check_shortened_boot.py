#!/usr/bin/env python3
"""Fresh complete finite startup replay and frame decoding, no runtime claim."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1] / "research_sub222/delivery/K221_Construction_2026-10-20"
source = BASE / "machine/k221.native.tm"
raw = source.read_bytes()
assert hashlib.sha256(raw).hexdigest() == "e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc"
table = {}
for line in raw.decode().splitlines():
    if line and not line.startswith("#"):
        q, b, w, d, z = line.split()
        if int(q) != 50:
            table[int(q), int(b)] = (int(w), 1 if d == "R" else -1, 75 if int(z) == 50 else int(z))
states = {q for q, _ in table}
assert len(states) == 220
assert set(table) == {(q, b) for q in states for b in (0, 1)}
assert all(z in states | {254} for _, _, z in table.values())

steps = 108420
origin = steps + 1
tape = bytearray(2 * origin + 1)
q, h = 0, origin
for tick in range(steps):
    w, d, q = table[q, tape[h]]
    tape[h] = w
    h += d
    assert q != 254
h -= origin
support = {i - origin for i, b in enumerate(tape) if b}
assert (q, h) == (84, -6)
assert min(support) == h - 1
header = min(x for x in support if x >= h)
assert header == 66
values, p = [], header + 1
while p <= max(support):
    assert p not in support
    p += 1
    start = p
    while p in support:
        p += 1
    assert p > start
    values.append(p - start - 1)
assert len(values) == 70
expected = {h - 1, header}
p = header + 1
for value in values:
    p += 1
    expected.update(range(p, p + value + 1))
    p += value + 1
assert support == expected
physical_map = [6, 2, 0, 4, 3, 7, 8, 5, 1]
logical = [values[i] for i in physical_map]
assert logical == [4, 3, 0, 0, 3, 0, 0, 0, 0]
assert values[9:] == [1] * 61
assert header - h - 64 == 8
receipt = {
    "status": "EXACT_FINITE_SHORTENED_SCANNER_STARTUP_PASS_NOT_RUNTIME",
    "baseline_table_sha256": hashlib.sha256(raw).hexdigest(),
    "transformation": "Delete state50 and redirect every target50 to75.",
    "working_states": len(states), "steps": steps, "state": q, "head": h,
    "header": header, "extra_gap": 8, "physical_registers": values[:9],
    "logical_registers": logical, "spares": values[9:],
    "complete_one_cells": sorted(support), "all_other_cells": 0,
    "known_runtime_status": "The unchanged source has a six-zero-PC runtime failure; this is not a correct 220-state candidate.",
}
(HERE / "shortened_boot_audit.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({k: v for k, v in receipt.items() if k not in ("spares", "complete_one_cells")}, indent=2))
