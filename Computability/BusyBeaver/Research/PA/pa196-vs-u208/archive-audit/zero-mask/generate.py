#!/usr/bin/env python3
"""Generate private Lean checks for the pinned archive's zero-mask certificate."""

import hashlib
import importlib.util
import json
import sys
from pathlib import Path
from zipfile import ZipFile

if len(sys.argv) != 3:
    raise SystemExit("usage: generate.py REPOSITORY PRIVATE_OUTPUT_DIRECTORY")
repo, out = map(Path, sys.argv[1:])
archive_path = repo / "docs/incoming/pa_tm_extended_research_2026-11-13.zip"
prefix = "pa_tm_extended_research_2026-11-13/auxiliary196/"
pins = {
    "core.py": "97522788b45f122ff34487331dae44aa0831b916564d528295b78b1c605c48c6",
    "inputs/PA196/Program.lean": "8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872",
    "zero_invariants.json": "e0a2011b994756fbf089debf19c562a60ba886e0910558284b0c7608b15b8bbd",
}
out.mkdir(parents=True, exist_ok=True)
with ZipFile(archive_path) as archive:
    for name, expected in pins.items():
        data = archive.read(prefix + name)
        if hashlib.sha256(data).hexdigest() != expected:
            raise SystemExit(f"archive member hash mismatch: {name}")
        target = out / "archive" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
program_path = repo / "Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean"
if hashlib.sha256(program_path.read_bytes()).hexdigest() != pins["inputs/PA196/Program.lean"]:
    raise SystemExit("archive and checked upstream Program.lean do not match")

# This is the archive's pinned parser. Its source-to-table correspondence is
# kernel-checked only for the explicitly generated sample rows below.
spec = importlib.util.spec_from_file_location("pinned_zero_core", out / "archive/core.py")
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)
_, instructions = core.program()
certificate = json.loads((out / "archive/zero_invariants.json").read_text())
masks = list(map(int, certificate["reachable_masks"]))
if len(masks) != 3812 or len(instructions) != 3812 or any(m < 0 or m.bit_length() > 512 for m in masks):
    raise SystemExit("unexpected source or certificate dimensions")

positive = [sum(1 << m for m in range(512) if (m >> r) & 1) for r in range(9)]
zero = [((1 << 512) - 1) ^ x for x in positive]
lines = ["import Transfer", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
         "def jumpCheck (s t : Nat) : Bool := maskSub s t"]
for begin in range(0, 3812, 8):
    checks = []
    for i in range(begin, min(begin + 8, 3812)):
        op, s = instructions[i], masks[i]
        if op[0] == "inc":
            _, r, q = op
            check = f"incCheck {s} {masks[q]} {positive[r]} {zero[r]} {2**r}"
        elif op[0] == "dec":
            _, r, q, p = op
            check = f"decCheck {s} {masks[q]} {masks[p]} {positive[r]} {zero[r]} {2**r}"
        elif op[0] == "jump":
            check = f"jumpCheck {s} {masks[op[1]]}"
        elif op[0] == "halt":
            check = "true"
        else:
            raise SystemExit(f"unexpected instruction at {i}: {op}")
        checks.append(f"({check})")
    lines.append(f"theorem chunk{begin} : (" + " &&\n".join(checks) + ") = true := by decide")
lines += ["#print axioms chunk0", "#print axioms chunk3808"]
(out / "Closure.lean").write_text("\n".join(lines) + "\n")

lines = ["import Transfer", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
         f"def site3692 : Nat := {masks[3692]}", f"def site25 : Nat := {masks[25]}",
         "theorem seed_present : site25.testBit 1 = true := by decide"]
for r in (3, 4, 5, 6):
    lines += [
        f"def zero{r} : Nat := {zero[r]}",
        f"theorem zero{r}_meaning : ∀ m : Fin 512, zero{r}.testBit m.val = !m.val.testBit {r} := by decide",
        f"theorem zero{r}_subset : maskSub site3692 zero{r} = true := by decide",
        f"theorem site3692_reg{r}_zero (m : Fin 512) (hm : site3692.testBit m.val = true) : m.val.testBit {r} = false := by",
        f"  have hz := maskSub_sound zero{r}_subset hm",
        f"  rw [zero{r}_meaning m] at hz",
        "  simpa using hz",
    ]
lines += ["#print axioms seed_present"] + [f"#print axioms site3692_reg{r}_zero" for r in (3, 4, 5, 6)]
(out / "Zero.lean").write_text("\n".join(lines) + "\n")

lines = ["import PA196.Program", "open M6.Source", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0"]
for i in [*range(32), 3692]:
    op = instructions[i]
    if op[0] == "inc":
        value = f".inc {op[1]} (some {op[2]})"
    elif op[0] == "dec":
        value = f".dec {op[1]} (some {op[2]}) (some {op[3]})"
    elif op[0] == "jump":
        value = f".jump (some {op[1]})"
    elif op[0] == "halt":
        value = ".halt"
    else:
        raise SystemExit(f"unexpected instruction at {i}: {op}")
    lines.append(f"theorem sourceRow{i} : resolveAt PA196.Program.sites {i} = some ({value}) := by rw [PA196.Program.resolve_tree]; rfl")
lines += ["#print axioms sourceRow0", "#print axioms sourceRow3692"]
(out / "Rows.lean").write_text("\n".join(lines) + "\n")
print("Generated checks for 3812 extracted rows, 477 closure chunks, and 33 upstream source rows.")
