import BusyBeaver.ZFC.Dag222

/-!
The structured register program of the 219-state machine (`dag219`).

`dag222` with the equality test, node 123, replaced by Source 140's routine
`E = (L, R)`, `L = (A, D6)`, `A = (D5, U)`, `U = (P, B)`, `P = (D6, C2)`, `R = (Z, U)`,
`Z = (D5, C1)` on the appended nodes 461-466 (`U` is shared); `D6` and `D5` decrement `s1` and
`p2`. Every other node is dag222's (the routine is from `make_dag219.py`).
-/

namespace SetTheory.BusyBeaver.ZFC.Dag219

open RMDag

/-- Source 140's equality test: `E` at 123, `P, U, A, L, Z, R` at 461-466. -/
def eqNodes : Nat → Option (Edge × Edge)
  | 123 => some (.node 464, .node 466)
  | 461 => some (.decnz 6, .cont 2)
  | 462 => some (.node 461, .brk 1)
  | 463 => some (.decnz 5, .node 462)
  | 464 => some (.node 463, .decnz 6)
  | 465 => some (.decnz 5, .cont 1)
  | 466 => some (.node 465, .node 462)
  | _ => none

def dagNodes (n : Nat) : Edge × Edge := (eqNodes n).getD (Dag222.dagNodes n)

def dag219 : Prog := ⟨dagNodes, 0⟩

end SetTheory.BusyBeaver.ZFC.Dag219
