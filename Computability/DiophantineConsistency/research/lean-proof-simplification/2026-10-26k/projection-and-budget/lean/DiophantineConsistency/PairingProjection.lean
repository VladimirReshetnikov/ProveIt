import Mathlib.Logic.Equiv.Basic

/-! Projection graphs of the inverse of a product equivalence. -/
namespace DiophantineConsistency.PairingProjection

theorem exists_right_iff {A B C : Type*} (e : A × B ≃ C) (z : C) (a : A) :
    (∃ b, z = e (a, b)) ↔ a = (e.symm z).1 := by
  simp only [← e.symm_apply_eq, Prod.ext_iff]
  simp [eq_comm]

theorem exists_left_iff {A B C : Type*} (e : A × B ≃ C) (z : C) (b : B) :
    (∃ a, z = e (a, b)) ↔ b = (e.symm z).2 := by
  simp only [← e.symm_apply_eq, Prod.ext_iff]
  simp [eq_comm]

end DiophantineConsistency.PairingProjection
