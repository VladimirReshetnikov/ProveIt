#!/usr/bin/env python3
"""Render the earlier 35 formal-label templates as Lean-checked local runs.

The JSON is data. This script does not execute any archived program or trust a
trace as a proof: Lean reduces runLocal against the unchanged literal table.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def bit(value):
    if value not in (0, 1, False, True):
        raise ValueError(f"Invalid bit: {value!r}")
    return "true" if value else "false"


def seg(value):
    kind = value[0]
    if kind == "b" and len(value) == 2:
        return f".bit {bit(value[1])}"
    if kind == "r" and len(value) == 4:
        if not all(isinstance(n, int) and n >= 0 for n in value[2:]):
            raise ValueError("Invalid run coefficients")
        return f".run {bit(value[1])} {value[2]} {value[3]}"
    if kind == "x" and value == ["x", "none", 0]:
        return ".box (.plain .none)"
    raise ValueError(f"Unsupported segment: {value!r}")


def segs(values):
    return "[" + ", ".join(seg(v) for v in values) + "]"


def word(value):
    if not isinstance(value, str) or any(c not in "01" for c in value):
        raise ValueError("Invalid binary word")
    return "[" + ", ".join(bit(int(c)) for c in value) + "]"


def conf(value):
    q, onl, left, right = value
    if not isinstance(q, int) or q < 0:
        raise ValueError("Invalid state")
    return f"({q}, {bit(onl)}, {segs(left)}, {segs(right)})"


def render(data, digest):
    records = data["templates_data"]
    if len(records) != 35 or [r["id"] for r in records] != list(range(35)):
        raise ValueError("Expected precisely the ordered 35 inherited templates")
    if data["native_to_formal"] != {"301": 102, "302": 120, "254": 230}:
        raise ValueError("Unexpected label binding")
    rows = []
    for r in records:
        q, onl, left, right = r["pre_home"]
        if (q, onl, left) != (2, True, []):
            raise ValueError("A template does not end at the exact empty-left Home port")
        n = r["steps"]
        if not isinstance(n, int) or n <= 0:
            raise ValueError("Invalid step count")
        key = r["key"]
        if key[3] not in ("CC", "CB") or not isinstance(key[4], int) or key[4] < 0:
            raise ValueError("Invalid source operation")
        rows.append(f"  ⟨{r['id']}, {n}, {conf(r['start'])}, {segs(right)}, "
                    f"{word(key[2])}, {bit(key[3] == 'CC')}, {key[4]}, {word(key[6])}⟩")
    header = '''import LeftFrameContract
import BusyBeaver.ZFC.KTable215

/-!
Kernel equations for the 35 inherited round13 local templates.
The source data already uses the maintained table's labels (301 -> 102,
302 -> 120, halt 254 -> 230). No native-table trace is accepted on trust.
This generated file checks runLocal directly against KTableCore.tm215.
Attribution: round13-left-frame/runtime/FORMAL_TEMPLATES.json.
Input SHA-256: DIGEST
-/

namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215
open KZip KRuntimeCore KLeftFrame KTableCore

structure LocalTemplate where
  id : Nat
  steps : Nat
  start : SConf
  right : List Seg
  suffix : List Bool
  isContinue : Bool
  controlArg : Nat
  result : List Bool
  deriving DecidableEq, Repr

def templates : List LocalTemplate := [
'''.replace("DIGEST", digest)
    footer = '''
]

def checkTemplate (t : LocalTemplate) : Bool :=
  runLocal tm215 none t.steps t.start == some (2, true, [], t.right)

theorem counts : templates.length = 35 ∧ (templates.map LocalTemplate.steps).sum = 444 ∧
    templates.map LocalTemplate.id = List.range 35 := by
  decide +kernel

theorem all_checked : templates.all checkTemplate = true := by
  decide +kernel

theorem template_checked {t : LocalTemplate} (ht : t ∈ templates) :
    runLocal tm215 none t.steps t.start = some (2, true, [], t.right) := by
  have h : checkTemplate t = true := List.all_eq_true.mp all_checked t ht
  simpa only [checkTemplate, beq_iff_eq] using h

/-- One checked local run serves every admissible prefix, gap and register file.
The premises are the unchanged runtime boxes and Home contracts. -/
theorem every_template_sound (B : BoxLemmas tm215)
    (rows : KHome.Rows tm215) (hb : KHome.Boundary tm215)
    {t : LocalTemplate} (ht : t ∈ templates)
    (P : List Bool) {j : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    Reach1 tm215
      (conc n vs (addLeft (P.reverse.map .bit ++ [.bit true]) t.start))
      (zc 84 [true] (P ++ flat n vs t.right)) :=
  local_home_sound B rows hb n hv P hs (template_checked ht)

#print axioms counts
#print axioms all_checked
#print axioms template_checked
#print axioms every_template_sound
end SetTheory.BusyBeaver.ZFC.KLeftFrame215
'''
    return header + ",\n".join(rows) + footer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--templates", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    raw = args.templates.read_bytes()
    text = render(json.loads(raw), hashlib.sha256(raw).hexdigest())
    args.output.write_text(text, encoding="utf-8")
    print(json.dumps({"output": str(args.output), "bytes": len(text.encode()),
                      "templates": 35, "symbolic_steps": 444}))


if __name__ == "__main__":
    main()
