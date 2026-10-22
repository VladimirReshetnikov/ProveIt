#!/usr/bin/env python3
"""Generate a literal AX adapter. AXWord.lean is maintained shared proof source.

Usage is unchanged: generate_l2axiomsdom.py NODES_JSON OUT_LEAN [perm].
The generator checks the input's supported chain shape. The Lean axWord_checked
proof is the authority binding the shared semantic word to the literal program.
An unexpected semantic word is rejected by that kernel check.
"""
import json
import sys
from pathlib import Path

src, out = sys.argv[1:3]
variant = sys.argv[3] if len(sys.argv) > 3 else "dom"
assert variant in {"dom", "perm"}
d = json.loads(Path(src).read_text())
nodes = {int(k): v for k, v in d["nodes"].items()}
supported = {166, 121, 168, 171, 119, 181, 180, 182, 218, 178, 183, 176, 175}
seen, n = set(), 236
while n != 457:
    assert n not in seen, "cyclic AX chain"
    seen.add(n)
    left, right = nodes[n]
    assert left[0] == right[0] == "N" and left[1] in supported
    n = right[1]
assert len(seen) == 156, "unexpected AX length"
assert [nodes[n][0][1] for n in [457, 458, 459, 460]] == [192, 131, 211, 197]
assert nodes[460][1] == ["N", 131]

TEMPLATE = r"""import BusyBeaver.ZFC.L2Perm
import BusyBeaver.ZFC.EnumPerm
import BusyBeaver.ZFC.AXWord

/-! Literal binding of dagPerm's AX word to the shared symbolic AX proof. -/
namespace SetTheory.BusyBeaver.ZFC.L2Perm
open RMDag DagPerm
open L2K (AS enc Clean)

abbrev axWord := AXWord.axWord true
theorem axWord_checked : AXWord.axWordCheck dagPerm 236 axWord = true := by decide +kernel

def f236 (st : AS) : AS := AXWord.axWordEval axWord st

theorem l236 (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  AXWord.axWordRun
    (fun st hc a => tr (by cases a <;> rfl) (AXWord.AXAtom.run st hc a))
    (fun st hc => tr rfl (AXWord.l457 st hc)) axWord axWord_checked st hc

theorem c236 (st : AS) (hc : Clean st) : Clean (f236 st) := AXWord.axWordClean axWord st hc

theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumPerm.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        EnumPerm.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a
          t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := AXWord.ax_eval true np t S c a h pl

#print axioms l236
#print axioms ax_eval
end SetTheory.BusyBeaver.ZFC.L2Perm
"""
text = TEMPLATE
if variant == "dom":
    for old, new in [("dagPerm", "dagDom"), ("DagPerm", "DagDom"),
                     ("L2Perm", "L2Dom"), ("EnumPerm", "EnumDom"),
                     ("AXWord.axWord true", "AXWord.axWord false"),
                     ("AXWord.ax_eval true", "AXWord.ax_eval false")]:
        text = text.replace(old, new)
Path(out).write_text(text)
print("wrote", out, "shared AX adapter", variant)
