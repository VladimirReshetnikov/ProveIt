import DiophantineConsistency.QuadraticRegisterSystem

/-! # Relational attachments in one shared register and auxiliary-input context -/

namespace DiophantineConsistency.QuadraticRegisterSystem

open NaturalRegisterProgram

abbrev Slot {n : ℕ} (p : Program n) := Fin n ⊕ Fin p.nodes.length

def slotValue {n : ℕ} (p : Program n) (x : Fin n → ℕ) : Slot p → ℕ :=
  Sum.elim x (p.eval x)

@[simp] theorem cast_slotValue {n : ℕ} (p : Program n) (x : Fin n → ℕ) (i : Slot p) :
    (slotValue p x i : ℤ) = natAssignment x (p.eval x) i := by
  cases i <;> rfl

namespace System

variable {n : ℕ} {p : Program n}

/-- Add constraints in the existing input/auxiliary/register context. The
stored register program is shared, and no new gate witnesses are introduced. -/
def conjunction (s t : System p) : System p where
  rowCount := s.rowCount + t.rowCount
  row := Fin.addCases s.row t.row
  degree i := by
    refine Fin.addCases (fun j : Fin s.rowCount => ?_) (fun j : Fin t.rowCount => ?_) i
    · simpa only [Fin.addCases_left] using s.degree j
    · simpa only [Fin.addCases_right] using t.degree j

@[simp] theorem conjunction_rowCount (s t : System p) :
    (s.conjunction t).rowCount = s.rowCount + t.rowCount := rfl

theorem conjunction_holds (s t : System p) (x : Fin n → ℕ) :
    (s.conjunction t).Holds x ↔ s.Holds x ∧ t.Holds x := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [conjunction,Fin.addCases_left] using h (Fin.castAdd t.rowCount i)
    · intro i
      simpa only [conjunction,Fin.addCases_right] using h (Fin.natAdd s.rowCount i)
  · rintro ⟨hs,ht⟩ i
    refine Fin.addCases (fun j : Fin s.rowCount => ?_) (fun j : Fin t.rowCount => ?_) i
    · simpa only [conjunction,Fin.addCases_left] using hs j
    · simpa only [conjunction,Fin.addCases_right] using ht j

/-- Instantiate a gate-free local relation at existing input or register slots.
Only variable indices are copied; previously stored computations stay shared. -/
def instantiate {ports : ℕ} (s : System (Program.empty : Program ports))
    (p : Program n) (port : Fin ports → Slot p) : System p where
  rowCount := s.rowCount
  row i := (s.row i).rename (Sum.elim port Fin.elim0)
  degree i := by
    rw [NaturalRegisterRelation.rename_toPolynomial]
    exact (MvPolynomial.totalDegree_rename_le _ _).trans (s.degree i)

@[simp] theorem instantiate_rowCount {ports : ℕ} (s : System (Program.empty : Program ports))
    (p : Program n) (port : Fin ports → Slot p) :
    (s.instantiate p port).rowCount = s.rowCount := rfl

theorem instantiate_holds {ports : ℕ} (s : System (Program.empty : Program ports))
    (p : Program n) (port : Fin ports → Slot p) (x : Fin n → ℕ) :
    (s.instantiate p port).Holds x ↔ s.Holds (fun i => slotValue p x (port i)) := by
  have he : natAssignment x (p.eval x) ∘ Sum.elim port Fin.elim0 =
      natAssignment (fun i => slotValue p x (port i))
        ((Program.empty : Program ports).eval (fun i => slotValue p x (port i))) := by
    funext i
    cases i with
    | inl j => exact (cast_slotValue p x (port j)).symm
    | inr j => exact j.elim0
  simp only [Holds,instantiate,Expr.eval_rename,he]
  rfl

/-- A conjunction retains the program's exact gate-witness count. -/
theorem conjunction_witnessCount (s t : System p) :
    (s.conjunction t).representation.witnessCount = p.nodes.length := rfl

end System
end DiophantineConsistency.QuadraticRegisterSystem
