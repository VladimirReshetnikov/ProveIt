"""Generate or check the literal Lean 254-state benchmark from the pinned table.

From the repository root:
  uv run --no-project python Computability/BusyBeaver/Research/ZFC/generate_table254.py --check

The source hash, state labels, all 508 transitions, and start/halt conventions
are checked before generating. No third-party executable code is imported.
The default source is the unchanged vendored snapshot; --source accepts a
separate recovered copy. Lean remains responsible for checking the emitted
proof terms. --check writes nothing and rejects any output difference.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from audit_tm import parse_table

SHA256 = "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"
ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / "lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm"
OUTPUT = ROOT / "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Table254.lean"

HEADER = r'''import BusyBeaver.Core

/-!
Literal Mira-Cult 254-state benchmark in the repository's Lean machine model.

Generated from lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm,
upstream jeff87654/busy-beaver commit
297ab8df7e5de329605c3875b4934643b371a5e3.
Source SHA-256:
d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb.

Mira-Cult designed the machine; Jeff supplied the separate upstream Coq
verification. This generated Lean representation imports only BusyBeaver.Core
and proves finite table facts. It does not import the Coq development or prove
any ZFC consistency endpoint, whole-machine simulation, or new state bound.
Operational states are Fin 254. Source terminal label 254 becomes `none`;
the final write/move still occur, exactly as in BusyBeaver.Core.
-/

namespace SetTheory.BusyBeaver.ZFC

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Write bit, head move, numerical successor (254 is terminal). -/
abbrev RawAction254 := Bool × Move × Nat

/-- Each pair stores the read-zero and read-one actions, in numerical state order. -/
def rawTable254 : Array (RawAction254 × RawAction254) := #[
'''

FOOTER = r'''
]

/-- Finite size check, proved by kernel reduction. -/
theorem rawTable254_size : rawTable254.size = 254 := by decide

/-- Every numerical successor is a working state or the designated terminal. -/
theorem rawTable254_targets_bounded :
    rawTable254.toList.all (fun row =>
      decide (row.1.2.2 ≤ 254 ∧ row.2.2.2 ≤ 254)) = true := by decide

/-- There is exactly one transition into the source terminal label. -/
theorem rawTable254_halt_edge_count :
    ((rawTable254.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 254)).length = 1 := by decide

/-- The fallback is unreachable for Fin 254 indices, by rawTable254_size. -/
def rawAction254 (state : Fin 254) (bit : Bool) : RawAction254 :=
  let row := rawTable254.getD state.val
    ((false, .right, 254), (false, .right, 254))
  if bit then row.2 else row.1

/-- Map the numerical halt label to the existing separate terminal convention. -/
def action254 (state : Fin 254) (bit : Bool) : Action 254 :=
  let raw := rawAction254 state bit
  { write := raw.1
    move := raw.2.1
    next := if h : raw.2.2 < 254 then some ⟨raw.2.2, h⟩ else none }

/-- The literal benchmark uses 254 operational states and two tape symbols. -/
def machine254 : Machine 254 where
  transition := action254

/-- The same table at the typed-state interface used by StateReduction.lean. -/
def typedMachine254 : TypedMachine (Fin 254) where
  transition state bit :=
    let action := action254 state bit
    { write := action.write, move := action.move, next := action.next }

/-- A direct sanity check of the first blank-tape transition. -/
theorem machine254_initial_action :
    machine254.transition ⟨0, by decide⟩ false =
      { write := true, move := .left, next := some ⟨1, by decide⟩ } := by decide

#print axioms rawTable254_size
#print axioms rawTable254_targets_bounded
#print axioms rawTable254_halt_edge_count
#print axioms machine254_initial_action

end SetTheory.BusyBeaver.ZFC
'''


def generate(source: Path) -> str:
    data = source.read_bytes()
    if hashlib.sha256(data).hexdigest() != SHA256:
        raise ValueError("source differs from the pinned literal table")
    machine = parse_table(data.decode("utf-8"))
    if machine.start != 0 or machine.halt != 254 or machine.states != list(range(254)):
        raise ValueError("unexpected start, terminal or working-state labels")
    rows = []
    for state in machine.states:
        def action(bit: int) -> str:
            edge = machine.rows[state, bit]
            write = "true" if edge.write else "false"
            move = "right" if edge.move == 1 else "left"
            return f"({write}, .{move}, {edge.target})"
        comma = "," if state < 253 else ""
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
            parser.error("Lean output differs from the pinned-table generation")
        print("Checked 254 Lean rows against all 508 pinned source transitions")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result, encoding="utf-8")
        print(f"Generated {args.output}")


if __name__ == "__main__":
    main()
