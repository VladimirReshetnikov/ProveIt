#!/usr/bin/env python3
"""Extract four standalone declarations from the pinned B=65537 source."""
import hashlib
import json
import pathlib
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")
HERE = pathlib.Path(__file__).resolve().parent
PARENT = HERE.parent / "trace74-next-scale-kernel-certificate/observations/B65537/Certificate.lean"
EXPECTED = "63eafa7643cb1f0505739b7b6902f9b457d5e4af9be19bac3a79573f281a6a2c"
raw = PARENT.read_bytes()
if hashlib.sha256(raw).hexdigest() != EXPECTED:
    raise SystemExit("frozen parent certificate hash mismatch")
lines = raw.decode().splitlines(keepends=True)
assert lines[:4] == ["import Mathlib.Data.Nat.GCD.Basic\n", "set_option maxRecDepth 65536\n",
                     "set_option maxHeartbeats 0\n", "namespace Trace74ScaledCertificate\n"]
assert lines[4].startswith("def modulus : Nat := ")
assert lines[5].startswith("def coeffL : Nat := ") and lines[6].startswith("def coeffD : Nat := ")
assert lines[7].startswith("def step ") and lines[8].startswith("  let A := ")
assert lines[9].startswith("  let C := ") and lines[10].startswith("  if bit then ")

def line(prefix):
    found = [s for s in lines if s.startswith(prefix)]
    assert len(found) == 1, prefix
    return found[0]

out = HERE / "observations"
out.mkdir(exist_ok=True)
result = {}
for name, selected in {
    "transition00": ["def state00 : ", "def state01 : ", "theorem transition00 : "],
    "transition15": ["def state15 : ", "def state16 : ", "theorem transition15 : "],
    "transition31": ["def state31 : ", "def state32 : ", "theorem transition31 : "],
    "bezout": ["def state32 : ", "def bezoutS : ", "def bezoutT : ", "theorem bezout : "],
}.items():
    folder = out / name
    folder.mkdir(exist_ok=True)
    extracted = [line(s) for s in selected]
    assert extracted[-1].rstrip().endswith(":= by decide")
    body = "".join(lines[:11] + extracted + [f"#print axioms Trace74ScaledCertificate.{name}\n", "end Trace74ScaledCertificate\n"])
    destination = folder / "Certificate.lean"
    destination.write_text(body, encoding="utf-8")
    result[name] = {"source_sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
                    "extracted_line_sha256": [hashlib.sha256(s.encode()).hexdigest() for s in extracted]}
(HERE / "manifest.json").write_text(json.dumps({"parent_sha256": EXPECTED, "declarations": result}, indent=2, sort_keys=True) + "\n")
print(json.dumps({"parent_sha256": EXPECTED, "declarations": result}, sort_keys=True))
