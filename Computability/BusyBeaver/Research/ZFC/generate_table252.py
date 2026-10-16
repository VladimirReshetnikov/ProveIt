"""Generate or check the experimental literal 252-state research table in Lean.

The frozen source hash, 252 working labels, 504 transitions, terminal edges,
and start/halt conventions are checked before generation. No third-party
executable code is imported. --check writes nothing. Lean must separately
check the emitted finite proof terms; no consistency calibration is supplied.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from audit_tm import parse_table

SHA256 = "58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142"
ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / "Computability/BusyBeaver/Research/ZFC/raw-candidate-252.tm"
OUTPUT = ROOT / "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Table252.lean"

HEADER = r'''import BusyBeaver.Core

/-!
Experimental literal 252-state research candidate in the Lean machine model.

Generated from Computability/BusyBeaver/Research/ZFC/raw-candidate-252.tm.
Source SHA-256:
58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142.

The named source is AX-raw_equality_free_C_G_shared_dual_base3.tm,
SHA-256 06feea82f1ea6cbd7a93458d00e76c4afb14ab18e1cade3bb4afe1740dc48cab.
It is an edited public Wade-backend research candidate, not the Mira-Cult
254-state benchmark. See raw_candidate_252.md and raw-candidate-252-audit.json
under Computability/BusyBeaver/Research/ZFC for provenance and limitations.

The sole missing named row, 1.inc/read1, was filled with write1, right, halt
before canonical numbering. It is row 13/read1 here. Under undefined-row
halting this preserves halting and the final tape, adding one final head move.
Working states are Fin 252; numerical terminal 252 maps to `none`, retaining
the final write and move of BusyBeaver.Core. There are two terminal edges.

Only finite table facts are represented below. No whole-compiler simulation,
proof-search correctness, consistency calibration, or ZFC endpoint is proved.
In particular, the numerical size is not a verified improvement on the
254-state ZFC-consistency machine.
-/

namespace SetTheory.BusyBeaver.ZFC

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Write bit, head move, numerical successor (252 is terminal). -/
abbrev RawAction252 := Bool × Move × Nat

/-- Read-zero/read-one actions in numerical working-state order. -/
def rawTable252 : Array (RawAction252 × RawAction252) := #[
'''

FOOTER = r'''
]

/-- Finite size check by kernel reduction. -/
theorem rawTable252_size : rawTable252.size = 252 := by decide

/-- The literal binary table contains exactly 504 transition actions. -/
theorem rawTable252_transition_count :
    (rawTable252.toList.flatMap (fun row => [row.1, row.2])).length = 504 := by decide

/-- Every successor is a working state or the designated terminal. -/
theorem rawTable252_targets_bounded :
    rawTable252.toList.all (fun row =>
      decide (row.1.2.2 ≤ 252 ∧ row.2.2.2 ≤ 252)) = true := by decide

/-- Exactly two actions enter the source terminal label. -/
theorem rawTable252_halt_edge_count :
    ((rawTable252.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 252)).length = 2 := by decide

/-- The fallback is unreachable at Fin 252 indices, by rawTable252_size. -/
def rawAction252 (state : Fin 252) (bit : Bool) : RawAction252 :=
  let row := rawTable252.getD state.val
    ((false, .right, 252), (false, .right, 252))
  if bit then row.2 else row.1

/-- Interpret the numerical halt label with the separate terminal convention. -/
def action252 (state : Fin 252) (bit : Bool) : Action 252 :=
  let raw := rawAction252 state bit
  { write := raw.1
    move := raw.2.1
    next := if h : raw.2.2 < 252 then some ⟨raw.2.2, h⟩ else none }

/-- The frozen experimental table, without a proof-search calibration. -/
def machine252 : Machine 252 where
  transition := action252

/-- The same literal table at the typed-state interface. -/
def typedMachine252 : TypedMachine (Fin 252) where
  transition state bit :=
    let action := action252 state bit
    { write := action.write, move := action.move, next := action.next }

/-- Sanity check of the initial blank-tape action. -/
theorem machine252_initial_action :
    machine252.transition ⟨0, by decide⟩ false =
      { write := true, move := .right, next := some ⟨1, by decide⟩ } := by decide

/-- The formerly undefined read-one row preserves its read bit and halts. -/
theorem machine252_totalized_action :
    machine252.transition ⟨13, by decide⟩ true =
      { write := true, move := .right, next := none } := by decide

#print axioms rawTable252_size
#print axioms rawTable252_transition_count
#print axioms rawTable252_targets_bounded
#print axioms rawTable252_halt_edge_count
#print axioms machine252_initial_action
#print axioms machine252_totalized_action

end SetTheory.BusyBeaver.ZFC
'''


def generate(source: Path) -> str:
    data = source.read_bytes()
    if hashlib.sha256(data).hexdigest() != SHA256:
        raise ValueError("source differs from the frozen experimental table")
    machine = parse_table(data.decode("utf-8"))
    if (machine.start != 0 or machine.halt != 252 or
            machine.states != list(range(252)) or len(machine.rows) != 504):
        raise ValueError("unexpected state labels, transition count, start or terminal")
    if any(edge.target > 252 for edge in machine.rows.values()):
        raise ValueError("out-of-range numerical successor")
    if {key for key, edge in machine.rows.items() if edge.target == 252} != {(13, 1), (166, 1)}:
        raise ValueError("unexpected terminal edges")
    rows = []
    for state in machine.states:
        def action(bit: int) -> str:
            edge = machine.rows[state, bit]
            write = "true" if edge.write else "false"
            move = "right" if edge.move == 1 else "left"
            return f"({write}, .{move}, {edge.target})"
        comma = "," if state < 251 else ""
        rows.append(f"  ({action(0)}, {action(1)}){comma} -- {state}")
    return HEADER + "\n".join(rows) + FOOTER


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = generate(args.source)
    if args.check:
        if args.output.read_text(encoding="utf-8") != result:
            parser.error("Lean output differs from the frozen-table generation")
        print("Checked 252 Lean rows against all 504 frozen source transitions")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result, encoding="utf-8")
        print(f"Generated {args.output}")


if __name__ == "__main__":
    main()
