#!/usr/bin/env python3
"""Generate only literal Lean data; all semantic claims are kernel checked."""
from pathlib import Path
from check_marker_certificate import parse, OLD_HASH, NEW_HASH

HERE = Path(__file__).resolve().parent
old_start, old, old_hash = parse(HERE / 'k215.native.tm')
new_start, new, new_hash = parse(HERE / 'cm215.native.tm')
assert (old_start, new_start, old_hash, new_hash) == (0, 0, OLD_HASH, NEW_HASH)
assert set(old) == set(new)
states = sorted({q for q, b in old})

def row(x):
    w, d, q = x
    return f'some ⟨{str(bool(w)).lower()}, {str(d == 1).lower()}, {q}⟩'

def table(name, rows):
    text = [f'def {name} : TM := fun q b =>', '  match q.val with']
    for q in states:
        text.append(f'  | {q} => if b then {row(rows[q, 1])} else {row(rows[q, 0])}')
    text.append('  | _ => none')
    return '\n'.join(text)

header = '''import MarkerTransfer

/-!
Literal native tables transcribed from the SHA-256-pinned K215 and CM215 files.
The native labels are represented in Fin 303. Only 215 labels have outgoing
rows; holes and the distinguished halt label 254 have no row. No added
working states are hidden in the ambient finite type.

K215: %s
CM215: %s
-/
namespace CM215Exact
open MarkerTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
''' % (OLD_HASH, NEW_HASH)
trailer = '''

theorem facts : Facts old new where
  common := by decide
  old52 := by decide
  old176 := by decide
  new52 := by decide
  new176 := by decide
  new129 := by decide
  new185 := by decide
  in52 := by decide
  in176 := by decide
  in156 := by decide

def workingCount (M : TM) : Nat :=
  ((List.finRange 303).filter fun q => (M q false).isSome || (M q true).isSome).length

theorem old_count : workingCount old = 215 := by decide
theorem new_count : workingCount new = 215 := by decide

theorem old_total_on_working : ∀ q, (old q false).isSome = (old q true).isSome := by decide
theorem new_total_on_working : ∀ q, (new q false).isSome = (new q true).isSome := by decide

def closedRow (M : TM) : Option Row → Prop
  | none => True
  | some r => r.target = 254 ∨ (M r.target false).isSome = true

instance (M : TM) (r : Option Row) : Decidable (closedRow M r) := by
  cases r <;> unfold closedRow <;> infer_instance

theorem old_closed : ∀ q b, closedRow old (old q b) := by decide
theorem new_closed : ∀ q b, closedRow new (new q b) := by decide

theorem old_halt : ∀ b, old 254 b = none := by decide
theorem new_halt : ∀ b, new 254 b = none := by decide

/-- Whole-tape equivalence for the two exact literal tables, from native start 0. -/
theorem all_tapes_equihalt (h : Int) (t : Tape) :
    (∃ n, Halt old (PositiveSimulation.iter (next old) n ⟨0, h, t⟩)) ↔
    (∃ n, Halt new (PositiveSimulation.iter (next new) n ⟨0, h, t⟩)) :=
  MarkerTransfer.all_tapes_equihalt facts h t

/-- Exact-table blank halting equivalence. This is a transfer theorem,
not a new formalization of the inherited numerical-calculus/ZFC calibration. -/
theorem blank_equihalt :
    (∃ n, Halt old (PositiveSimulation.iter (next old) n ⟨0, 0, fun _ => false⟩)) ↔
    (∃ n, Halt new (PositiveSimulation.iter (next new) n ⟨0, 0, fun _ => false⟩)) :=
  all_tapes_equihalt 0 (fun _ => false)

#print axioms facts
#print axioms old_count
#print axioms new_count
#print axioms all_tapes_equihalt
#print axioms blank_equihalt
end CM215Exact
'''
(HERE / 'CM215Exact.lean').write_text(header + '\n' + table('old', old) + '\n\n' + table('new', new) + trailer)
