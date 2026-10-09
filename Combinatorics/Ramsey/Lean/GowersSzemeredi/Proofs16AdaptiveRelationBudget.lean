import GowersSzemeredi.Proofs16DenseRelationBudget

/-! A scalar state simultaneously bounds domain rank, fixed frequencies,
and the exponent of the retained density. The cutoff and tolerance can
be arbitrary functions of that state. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def adaptiveRelationBudget (theta : Nat → Real) (R : Nat → Nat) (Q k d : Nat) : Nat :=
  d + denseRelationBudget (theta d) (R d) Q k d

/-- The common bound also pays for the exponent lost on recentering. -/
theorem adaptive_relation_density_step {alpha : Real} (ha : 0 ≤ alpha)
    (theta : Nat → Real) (R : Nat → Nat) (Q k d e : Nat) [NeZero Q]
    (he : e ≤ denseRelationBudget (theta d) (R d) Q k d) :
    alpha / (Q : Real)^(adaptiveRelationBudget theta R Q k d) ≤
      (alpha / (Q : Real)^d) / (Q : Real)^e := by
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  rw [div_div, ← pow_add]
  apply div_le_div_of_nonneg_left ha (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) (Nat.add_le_add_left he d)

end LeanProofs.GowersSzemeredi
