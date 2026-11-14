#!/usr/bin/env python3
"""Generate a bounded safe-startup certificate from pinned machine tables."""
import hashlib
import sys
from pathlib import Path
from zipfile import ZipFile

if len(sys.argv) != 3:
    raise SystemExit("usage: generate.py REPOSITORY PRIVATE_OUTPUT_DIRECTORY")
repo, out = map(Path, sys.argv[1:])
upstream = repo / "Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/data/pa196.tm"
archive = repo / "docs/incoming/pa_tm_extended_research_2026-11-13.zip"
pins = {
    3: "d5c1c2c69082971b23cc42da4c36f82f33ffb09f6482ca2f1c1ac6ab405249ca",
    4: "2be1986cbbac0c6e98cc4e515d83c2b9c7b063c3ac43fe30e919ce9d54e5c87d",
    5: "4433af83b56864fd5da9971e1bdee7236ceba5519160648f67ea8cb509558498",
    6: "2db09bb057682bdef3ded53dd086c2b24a3800ac74e4ae8a048eaf14b59b0536",
}
if hashlib.sha256(upstream.read_bytes()).hexdigest() != "e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8":
    raise SystemExit("unexpected upstream table")
if hashlib.sha256(archive.read_bytes()).hexdigest() != "960070a24cc17646d9e814e4f665b8e01337d363a4e345a036ea9dde8b82da76":
    raise SystemExit("unexpected archive")

def parse(raw):
    result = {}
    for line in raw.decode("ascii").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        if (q, b) in result or b not in (0, 1) or w not in (0, 1) or direction not in ("L", "R"):
            raise SystemExit("invalid transition row")
        result[q, b] = (w, int(direction == "R"), target)
    if set(result) != {(q, b) for q in range(196) for b in range(2)}:
        raise SystemExit("incomplete transition table")
    return result

rows = parse(upstream.read_bytes())
targets = [17, 113, 44, 21]
with ZipFile(archive) as z:
    for r, target in zip((3, 4, 5, 6), targets):
        name = f"pa_tm_extended_research_2026-11-13/auxiliary196/pa196_close_cd{r}.tm"
        data = z.read(name)
        if hashlib.sha256(data).hexdigest() != pins[r]:
            raise SystemExit(f"unexpected archive member: {name}")
        variant = parse(data)
        expected = dict(rows)
        expected[193, 1] = (1, 1, target)
        if variant != expected:
            raise SystemExit(f"candidate is not the expected one-row patch: {name}")

out.mkdir(parents=True, exist_ok=True)
lines = ["import PA196.Literal", "namespace CloseStartup", "def rows : Array (Nat × Nat × Nat) := #["]
lines += [f"  ({w},{d},{t})," for q in range(196) for b in range(2) for w, d, t in [rows[q, b]]]
lines += ["]", "end CloseStartup"]
(out / "Table.lean").write_text("\n".join(lines) + "\n")

def step(c):
    q, left, right = c
    if not q < 196 or (q == 193 and right % 2 == 1):
        raise SystemExit("startup visited a halted state or the changed row")
    w, direction, target = rows[q, right % 2]
    return (target, 2 * left + w, right // 2) if direction else (
        target, left // 2, left % 2 + 2 * (w + 2 * (right // 2)))

def conf(c):
    return f"({c[0]},{c[1]},{c[2]})"

chunks = []
c = (0, 0, 0)
for begin in range(0, 58154, 256):
    before = c
    count = min(256, 58154 - begin)
    for _ in range(count):
        c = step(c)
    chunks.append((count, before, c))
for base in range(0, len(chunks), 16):
    lines = ["import Common", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "namespace CloseStartup"]
    for i in range(base, min(base + 16, len(chunks))):
        count, before, after = chunks[i]
        lines.append(f"theorem seg{i} : safeRun {count} {conf(before)} = some {conf(after)} := by decide")
    lines += ["end CloseStartup"]
    (out / f"Batch{base // 16}.lean").write_text("\n".join(lines) + "\n")

lines = [f"import Batch{i}" for i in range((len(chunks) + 15) // 16)]
lines += ["set_option maxRecDepth 100000", "set_option maxHeartbeats 0", "namespace CloseStartup",
          "attribute [local irreducible] safeRun", "theorem certifiedTrace : safeRun 58154 (0,0,0) = some " + conf(c) + " := by"]
proof = f"seg{len(chunks) - 1}"
for i in range(len(chunks) - 2, -1, -1):
    proof = f"(safe_compose seg{i} {proof})"
lines += ["  exact " + proof,
          "theorem common_startup : ∃ final,",
          "    M6.Zip.run PA196.Literal.machine 58154 blank = some final ∧",
          "    (∀ v : Fin 4, M6.Zip.run (variant v) 58154 blank = some final) ∧",
          "    encodeZip final = " + conf(c) + " := by",
          "  exact safe_transfer 58154 blank _ certifiedTrace",
          "#print axioms certifiedTrace", "#print axioms common_startup", "end CloseStartup"]
(out / "Final.lean").write_text("\n".join(lines) + "\n")
print(f"Generated {len(chunks)} chunks; exact final numeric configuration: {conf(c)}")
