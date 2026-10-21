import BusyBeaver.ZFC.RMBisim

/-!
UNCOMPILED RESEARCH DRAFT. No Lean compilation has been performed.
This is a proposed semantic adapter, not the finite Boolean checker or data.
It reuses Bisim.halts_iff rather than developing a separate CFG semantics.
Interfaces inspected at e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad.
-/

namespace SetTheory.BusyBeaver.ZFC.CanonicalRowsDraft

open RegisterPath RMBisim

inductive Boundary where
  | halt
  | test (register : Nat)

def Boundary.edge : Boundary → Edge
  | .halt => .halt
  | .test r => .decnz r

structure Row where
  kind : Boundary
  left : List Bool
  right : List Bool
  positive : Nat := 0
  zero : Nat := 0

/-- Unlike ORel, membership is invariant under equivalent raw path aliases. -/
def Related {n : Nat} (t1 t2 : Tree) (rows : Fin n → Row)
    (P1 P2 : List Bool) : Prop :=
  ∃ i, tsite t1 P1 = some ((rows i).kind.edge, (rows i).left) ∧
    tsite t2 P2 = some ((rows i).kind.edge, (rows i).right)

def RowGood {n : Nat} (t1 t2 : Tree) (rows : Fin n → Row) (row : Row) : Prop :=
  match row.kind with
  | .halt => True
  | .test _ =>
      BranchGood t1 t2 (Related t1 t2 rows) (incPath row.left) (incPath row.right) ∧
      BranchGood t1 t2 (Related t1 t2 rows) (breakPath 1 row.left) (breakPath 1 row.right)

/-! Proposed Boolean checker. Its soundness adapter to RowGood is still to be
proved; these definitions are deliberately separate from rows_bisim below. -/

def lookupRow {n : Nat} (rows : Fin n → Row) (j : Nat) : Option Row :=
  if h : j < n then some (rows ⟨j, h⟩) else none

def matchesSite (t : Tree) (P : List Bool) (e : Edge) (Q : List Bool) : Bool :=
  match tsite t P with
  | some (e', Q') => decide (e' = e) && lbeq Q' Q
  | none => false

def checkBranch {n : Nat} (t1 t2 : Tree) (rows : Fin n → Row)
    (A B : List Bool) (j : Nat) : Bool :=
  match seg t1 segFuel A, seg t2 segFuel B, lookupRow rows j with
  | some (l1, P1), some (l2, P2), some row =>
      cntEq l1 l2 &&
        matchesSite t1 P1 row.kind.edge row.left &&
        matchesSite t2 P2 row.kind.edge row.right
  | _, _, _ => false

def checkRow {n : Nat} (t1 t2 : Tree) (rows : Fin n → Row) (row : Row) : Bool :=
  match row.kind with
  | .halt => true
  | .test _ =>
      checkBranch t1 t2 rows (incPath row.left) (incPath row.right) row.positive &&
      checkBranch t1 t2 rows (breakPath 1 row.left) (breakPath 1 row.right) row.zero

def checkAll {n : Nat} (t1 t2 : Tree) (rows : Fin n → Row) (initial : Nat) : Bool :=
  checkBranch t1 t2 rows [] [] initial &&
    (List.range n).all (fun j => match lookupRow rows j with
      | some row => checkRow t1 t2 rows row
      | none => false)

/-
Required generic checker lemmas, not claimed proved:
  matchesSite = true -> the corresponding exact tsite equation;
  checkBranch = true -> BranchGood (using cntEq_ok and lookupRow witness);
  checkRow = true -> RowGood;
  checkAll = true -> startup and every finite row is RowGood.

Halt rows impose no outgoing branch. A Related witness already supplies both
literal halt-site equations, so no unchecked halt inference is introduced.
One may additionally self-check every stored canonical path, as the Python
prototype does, although that is redundant for this semantic relation.
-/

/-- A finite row checker need only produce these existing semantic predicates. -/
theorem rows_bisim {n : Nat} {t1 t2 : Tree} {rows : Fin n → Row}
    (hs : BranchGood t1 t2 (Related t1 t2 rows) [] [])
    (hr : ∀ i, RowGood t1 t2 rows (rows i)) :
    Bisim t1 t2 (Related t1 t2 rows) := by
  refine ⟨hs, ?_⟩
  intro P1 P2 h
  obtain ⟨i, h1, h2⟩ := h
  have hi := hr i
  cases hk : (rows i).kind with
  | halt =>
      exact Or.inl ⟨(rows i).left, (rows i).right,
        by simpa only [hk, Boundary.edge] using h1,
        by simpa only [hk, Boundary.edge] using h2⟩
  | test r =>
      simp only [RowGood, hk] at hi
      exact Or.inr ⟨r, (rows i).left, (rows i).right,
        by simpa only [hk, Boundary.edge] using h1,
        by simpa only [hk, Boundary.edge] using h2, hi.1, hi.2⟩

/-
For the actual 1,426 rows, a NEW finite checker must still establish hr and hs.
For each branch, run existing seg, check equal register-increment counts,
then check each endpoint's tsite against the chosen successor row. This
provides Related and thus BranchGood. Use checked sharing to avoid decoding
and traversing the same long pointers repeatedly. Keep 512-bit decoding,
or store paths directly; the target contains paths longer than 127 bits.

Finally apply RMBisim.Bisim.halts_iff with t1/t2 equal to the two ptree values.
Neither tsite alias equivalence nor control-elimination needs a new theorem
for this adapter: the relation includes the exact required tsite equations,
and existing seg_run/seg_hn/Bisim.halts already provide their semantics.
-/

end SetTheory.BusyBeaver.ZFC.CanonicalRowsDraft
