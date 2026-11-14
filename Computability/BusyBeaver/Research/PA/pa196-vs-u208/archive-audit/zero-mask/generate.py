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

def lean_instruction(op):
    if op[0] == "inc":
        return f".inc {op[1]} (some {op[2]})"
    if op[0] == "dec":
        return f".dec {op[1]} (some {op[2]}) (some {op[3]})"
    if op[0] == "jump":
        return f".jump (some {op[1]})"
    if op[0] == "halt":
        return ".halt"
    raise SystemExit(f"unexpected instruction: {op}")

lines = ["import PA196.Program", "open M6.Source", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0"]
for i in [*range(32), 3692]:
    value = lean_instruction(instructions[i])
    lines.append(f"theorem sourceRow{i} : resolveAt PA196.Program.sites {i} = some ({value}) := by rw [PA196.Program.resolve_tree]; rfl")
lines += ["#print axioms sourceRow0", "#print axioms sourceRow3692"]
(out / "Rows.lean").write_text("\n".join(lines) + "\n")

# Small blocks keep each kernel reduction bounded when checking the actual
# table and certificate functions. All generated files remain in the temporary
# directory supplied by check.sh.
def blocks(values, convert):
    return ",\n".join("#[" + ", ".join(convert(v) for v in values[i:i + 16]) + "]"
                       for i in range(0, len(values), 16))

lines = ["import CertificateBridge", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
         "set_option exponentiation.threshold 512", "namespace PA196ZeroMask", "open M6.Source",
         "def instructionBlocks : Array (Array Instruction) := #[", blocks(instructions, lean_instruction), "]",
         "def certificateBlocks : Array (Array Nat) := #[", blocks(masks, str), "]",
         "def segmentedLookup (i : Nat) : Option Instruction :=\n"
         "  if i < 3812 then (instructionBlocks[i / 16]?).bind fun b => b[i % 16]? else none",
         "def segmentedCertificate (i : Nat) : Nat :=\n"
         "  ((certificateBlocks[i / 16]?).getD #[]).getD (i % 16) 0",
         "end PA196ZeroMask"]
(out / "SegmentBase.lean").write_text("\n".join(lines) + "\n")

headers = ["import SegmentBase", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
           "set_option exponentiation.threshold 512", "namespace PA196ZeroMask"]
for begin in range(0, 1024, 256):
    name = f"segment{begin}"
    statement = f"theorem {name} : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate ({begin}+i.val) = true := by decide"
    (out / f"{name}.lean").write_text("\n".join(headers + [statement, f"#print axioms {name}", "end PA196ZeroMask"]) + "\n")
for begin in range(1024, 3812, 64):
    name, size = f"part{begin}", min(64, 3812 - begin)
    statement = f"theorem {name} : ∀ i : Fin {size}, rowOK segmentedLookup segmentedCertificate ({begin}+i.val) = true := by decide"
    (out / f"{name}.lean").write_text("\n".join(headers + [statement, f"#print axioms {name}", "end PA196ZeroMask"]) + "\n")

for begin in range(1024, 3812, 256):
    total = min(256, 3812 - begin)
    parts = list(range(begin, begin + total, 64))
    conditions = []
    for part in parts:
        lo, hi = part - begin, min(part - begin + 64, total)
        conditions.append(f"i.val < {hi}" if lo == 0 else f"({lo} ≤ i.val ∧ i.val < {hi})")
    lines = [f"import part{part}" for part in parts]
    lines += ["set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "namespace PA196ZeroMask",
              f"theorem segment{begin} (i : Fin {total}) : rowOK segmentedLookup segmentedCertificate ({begin}+i.val) = true := by",
              "  have hi := i.isLt", "  have hc : " + " ∨ ".join(conditions) + " := by omega",
              "  rcases hc with " + " | ".join(f"h{k}" for k in range(len(parts)))]
    for part in parts:
        lo = part - begin
        lines += [f"  · have ht := part{part} ⟨i.val - {lo}, by omega⟩",
                  f"    have heq : {part} + (i.val - {lo}) = {begin} + i.val := by omega",
                  "    simpa only [heq] using ht"]
    lines += [f"#print axioms segment{begin}", "end PA196ZeroMask"]
    (out / f"aggregate{begin}.lean").write_text("\n".join(lines) + "\n")

names = [f"segment{begin}" for begin in range(0, 3812, 256)]
lines = ["import SegmentAssembly"]
lines += [f"import {'segment' if begin < 1024 else 'aggregate'}{begin}" for begin in range(0, 3812, 256)]
lines += ["set_option maxRecDepth 100000", "namespace PA196ZeroMask", "open M6.Source",
          "theorem segmentAll (pc : Nat) : rowOK segmentedLookup segmentedCertificate pc = true :=",
          "  allFromChunks " + " ".join(names) + " pc",
          "theorem archiveTableClosed : TableClosed segmentedLookup segmentedCertificate :=",
          "  table_closed_of_rows segmentedLookup segmentedCertificate segmentAll",
          "#print axioms segmentAll", "#print axioms archiveTableClosed", "end PA196ZeroMask"]
(out / "SegmentAll2.lean").write_text("\n".join(lines) + "\n")

# Independently bind the segmented instruction lookup to the optimized
# upstream trie resolver, using separate bounded kernel checks.
for begin in range(0, 3812, 64):
    name, size = f"resolver{begin}", min(64, 3812 - begin)
    lines = ["import ResolverCommon", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
             "namespace PA196ZeroMask",
             f"theorem {name} : ∀ i : Fin {size}, sourceFast ({begin}+i.val) = segmentedLookup ({begin}+i.val) := by decide",
             f"#print axioms {name}", "end PA196ZeroMask"]
    (out / f"{name}.lean").write_text("\n".join(lines) + "\n")

for begin in range(0, 3812, 256):
    total = min(256, 3812 - begin)
    parts = list(range(begin, begin + total, 64))
    conditions = []
    for part in parts:
        lo, hi = part - begin, min(part - begin + 64, total)
        conditions.append(f"i.val < {hi}" if lo == 0 else f"({lo} ≤ i.val ∧ i.val < {hi})")
    lines = [f"import resolver{part}" for part in parts]
    lines += ["set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "namespace PA196ZeroMask",
              f"theorem resolverSegment{begin} (i : Fin {total}) : sourceFast ({begin}+i.val) = segmentedLookup ({begin}+i.val) := by",
              "  have hi := i.isLt", "  have hc : " + " ∨ ".join(conditions) + " := by omega",
              "  rcases hc with " + " | ".join(f"h{k}" for k in range(len(parts)))]
    for part in parts:
        lo = part - begin
        lines += [f"  · have ht := resolver{part} ⟨i.val - {lo}, by omega⟩",
                  f"    have heq : {part} + (i.val - {lo}) = {begin} + i.val := by omega",
                  "    simpa only [heq] using ht"]
    lines += [f"#print axioms resolverSegment{begin}", "end PA196ZeroMask"]
    (out / f"resolverAggregate{begin}.lean").write_text("\n".join(lines) + "\n")

bases = list(range(0, 3812, 256))
conditions = []
for begin in bases:
    hi = min(begin + 256, 3812)
    conditions.append(f"pc < {hi}" if begin == 0 else f"({begin} ≤ pc ∧ pc < {hi})")
lines = [f"import resolverAggregate{begin}" for begin in bases]
lines += ["set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "namespace PA196ZeroMask", "open M6.Source",
          "theorem resolverWithin (pc : Nat) (hp : pc < 3812) : sourceFast pc = segmentedLookup pc := by",
          "  have hc : " + " ∨ ".join(conditions) + " := by omega",
          "  rcases hc with " + " | ".join(f"h{k}" for k in range(len(bases)))]
for begin in bases:
    lines += [f"  · have ht := resolverSegment{begin} ⟨pc - {begin}, by omega⟩",
              f"    have heq : {begin} + (pc - {begin}) = pc := by omega",
              "    simpa only [heq] using ht"]
lines += ["theorem resolver_binding (pc : Nat) : resolveAt PA196.Program.sites pc = segmentedLookup pc := by",
          "  by_cases hp : pc < 3812", "  · rw [PA196.Program.resolve_tree]", "    exact resolverWithin pc hp",
          "  · exact resolverOutside pc (by omega)", "#print axioms resolverWithin", "#print axioms resolver_binding",
          "end PA196ZeroMask"]
(out / "ResolverBinding.lean").write_text("\n".join(lines) + "\n")
print("Generated checks for 3812 extracted rows, table closure and resolver binding, and 33 source samples.")
