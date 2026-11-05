#!/usr/bin/env python3
"""Build a serial 32-step certificate from the pinned B=65537 source."""
import hashlib
import json
import pathlib
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")
HERE = pathlib.Path(__file__).resolve().parent
PARENT = HERE.parent / "trace74-next-scale-kernel-certificate/observations/B65537"
PARENT_SHA = "63eafa7643cb1f0505739b7b6902f9b457d5e4af9be19bac3a79573f281a6a2c"
TRACE_SHA = "03bae13ef4a9cfdc74126d171ed037fd03d62fb20121c255df494a343c99636d"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source, tracepath = PARENT / "Certificate.lean", PARENT / "trace.json"
assert sha(source) == PARENT_SHA and sha(tracepath) == TRACE_SHA
trace = json.loads(tracepath.read_text())
assert trace["B"] == 65537 and trace["index"] == 3056651345 and len(trace["bits"]) == 32
assert trace["bits"] == bin(3056651345)[2:] and len(trace["states"]) == 33
lines = source.read_text().splitlines(keepends=True)
assert lines[:4] == ["import Mathlib.Data.Nat.GCD.Basic\n", "set_option maxRecDepth 65536\n",
                     "set_option maxHeartbeats 0\n", "namespace Trace74ScaledCertificate\n"]

def original(prefix):
    found = [s for s in lines if s.startswith(prefix)]
    assert len(found) == 1, prefix
    return found[0]

assert lines[4] == f"def modulus : Nat := {trace['modulus']}\n"
assert lines[5] == f"def coeffL : Nat := {trace['L']}\n"
assert lines[6] == f"def coeffD : Nat := {trace['D']}\n"
for i, (x, y) in enumerate(trace["states"]):
    assert original(f"def state{i:02} : ") == f"def state{i:02} : Nat × Nat := ({x}, {y})\n"
for i, bit in enumerate(trace["bits"]):
    expected = f"theorem transition{i:02} : step state{i:02} {'true' if bit == '1' else 'false'} = state{i+1:02} := by decide\n"
    assert original(f"theorem transition{i:02} : ") == expected

src = HERE / "src"
if src.exists():
    raise SystemExit("refusing to overwrite existing source directory")
src.mkdir()
stages = []

def emit(name, content, predecessor, extracted):
    file = src / (name+".lean")
    file.write_text(content, encoding="utf-8")
    stages.append({"module": name, "source_sha256": sha(file), "predecessor": predecessor,
                   "extracted_line_sha256": [hashlib.sha256(x.encode()).hexdigest() for x in extracted]})

base = lines[:11] + [original("def state00 : ")]
emit("Trace74SplitCommon", "".join(base+["end Trace74ScaledCertificate\n"]), None, base[4:])
for i in range(32):
    name = f"Trace74SplitStep{i:02}"
    prev = "Trace74SplitCommon" if i == 0 else f"Trace74SplitStep{i-1:02}"
    extracted = [original(f"def state{i+1:02} : "), original(f"theorem transition{i:02} : ")]
    content = f"import {prev}\nset_option maxRecDepth 65536\nset_option maxHeartbeats 0\nnamespace Trace74ScaledCertificate\n"
    content += "".join(extracted)
    content += f"#print axioms Trace74ScaledCertificate.transition{i:02}\nend Trace74ScaledCertificate\n"
    emit(name, content, prev, extracted)

bits = ", ".join("true" if bit == "1" else "false" for bit in trace["bits"])
transitions = ", ".join(f"transition{i:02}" for i in range(32))
extracted = [original("def bezoutS : "), original("def bezoutT : "), original("theorem bezout : ")]
coprime_start = lines.index("theorem coprime : Nat.Coprime state32.2 modulus := by\n")
coprime_end = next(i for i in range(coprime_start, len(lines)) if lines[i].startswith("#print axioms"))
coprime = lines[coprime_start:coprime_end]
content = "import Trace74SplitStep31\nset_option maxRecDepth 65536\nset_option maxHeartbeats 0\nnamespace Trace74ScaledCertificate\n"
content += "".join(extracted+coprime)
content += f"def certificateBits : List Bool := [{bits}]\n"
content += "def certificateIndex : Nat := certificateBits.foldl (fun t bit => if bit then 2*t+1 else 2*t) 0\n"
content += "theorem certificate_initial : state00=(1%modulus,0%modulus) := by decide\n"
content += "theorem certificate_index : certificateIndex=3056651345 := by decide\n"
content += "theorem certificate_chain : certificateBits.foldl step state00=state32 := by\n"
content += f"  simp only [certificateBits, List.foldl_cons, {transitions}, List.foldl_nil]\n"
content += "theorem full_certificate : state00=(1%modulus,0%modulus) ∧ certificateIndex=3056651345 ∧ certificateBits.foldl step state00=state32 ∧ Nat.Coprime state32.2 modulus :=\n"
content += "  ⟨certificate_initial,certificate_index,certificate_chain,coprime⟩\n"
content += "#print axioms Trace74ScaledCertificate.full_certificate\nend Trace74ScaledCertificate\n"
emit("Trace74SplitFinal", content, "Trace74SplitStep31", extracted+coprime)
manifest = {"parent_source_sha256": PARENT_SHA, "trace_sha256": TRACE_SHA, "stages": stages}
(HERE / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True)+"\n")
print(f"derived {len(stages)} stages from pinned parent and trace")
