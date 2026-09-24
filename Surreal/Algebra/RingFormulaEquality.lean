import Mathlib.ModelTheory.Algebra.Ring.Basic

/-!
# Executable equality for native ring formulas

A structural Boolean equality test for the relation-free ring language,
including formulas with bound variables. This supports exact syntactic
recognition of the type in `odg:def:thm:saturation`.
-/

namespace Surreal.RingFormulaEquality
open FirstOrder FirstOrder.Language

local instance (n : ℕ) : DecidableEq (Language.ring.Functions n) :=
  inferInstanceAs (DecidableEq (ringFunc n))

/-- Compare native ring formulas by structural recursion. -/
def equal {α : Type*} [DecidableEq α] : {n : ℕ} →
    Language.ring.BoundedFormula α n → Language.ring.BoundedFormula α n → Bool
  | _, .falsum, .falsum => true
  | _, .equal a b, .equal c d => decide (a = c ∧ b = d)
  | _, .imp a b, .imp c d => equal a c && equal b d
  | _, .all a, .all b => equal a b
  | _, _, _ => false

/-- Boolean structural equality agrees with Lean equality. -/
@[simp] theorem equal_iff {α : Type*} [DecidableEq α] {n : ℕ}
    (φ ψ : Language.ring.BoundedFormula α n) : equal φ ψ = true ↔ φ = ψ := by
  induction φ with
  | falsum => cases ψ <;> simp [equal]
  | equal a b => cases ψ <;> simp [equal]
  | rel r ts => exact r.elim
  | imp a b ha hb => cases ψ <;> simp [equal, ha, hb]
  | all a ha => cases ψ <;> simp [equal, ha]

/-- A constructive decision procedure for syntactic equality. -/
def decidableEq {α : Type*} [DecidableEq α] {n : ℕ} :
    DecidableEq (Language.ring.BoundedFormula α n) := fun φ ψ =>
  decidable_of_iff (equal φ ψ = true) (equal_iff φ ψ)

end Surreal.RingFormulaEquality
