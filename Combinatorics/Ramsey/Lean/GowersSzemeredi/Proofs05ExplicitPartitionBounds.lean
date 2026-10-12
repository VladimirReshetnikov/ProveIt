import GowersSzemeredi.Proofs05ExplicitSchmidtRecurrence

/-! Bounds on the explicit partition constants, independent of the variety
structure and density-increment proofs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem two_le_ceil_multiaffinePartitionK (k h : Nat) :
    2 ≤ Nat.ceil (multiaffinePartitionK k h) := by
  exact_mod_cast (two_le_multiaffinePartitionK k h).trans (Nat.le_ceil _)

/-- The uniform base constant is at most `1 + k·B` under per-degree bounds `B`. -/
theorem uniformSchmidtK_le_of {k : Nat} {B : Real} (hB : ∀ j : Fin k, schmidtMonomialK j ≤ B) :
    uniformSchmidtK k ≤ 1 + k * B := by
  unfold uniformSchmidtK
  have : ∑ j : Fin k, schmidtMonomialK j ≤ ∑ _j : Fin k, B := Finset.sum_le_sum fun j _ => hB j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

/-- The uniform exponent constant is at most `1 + k·B` under per-degree bounds `B`. -/
theorem uniformSchmidtP_le_of {k B : Nat} (hB : ∀ j : Fin k, schmidtMonomialP j ≤ B) :
    uniformSchmidtP k ≤ 1 + k * B := by
  unfold uniformSchmidtP
  have : ∑ j : Fin k, schmidtMonomialP j ≤ ∑ _j : Fin k, B := Finset.sum_le_sum fun j _ => hB j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- The multiaffine base constant stays below any bound `B ≥ 2` on the uniform one. -/
theorem multiaffinePartitionK_le_of {k : Nat} {B : Real} (hB : uniformSchmidtK k ≤ B) (h2 : 2 ≤ B)
    (h : Nat) : multiaffinePartitionK k h ≤ B := by
  induction h with
  | zero => exact h2
  | succ h ih => exact max_le ih hB

/-- The multiaffine exponent constant is at most `(2(k+1)·P + 4)^h`. -/
theorem multiaffinePartitionP_le_pow (k h : Nat) :
    multiaffinePartitionP k h ≤ (2 * (k + 1) * uniformSchmidtP k + 4) ^ h := by
  induction h with
  | zero => exact le_rfl
  | succ h ih =>
    show multiaffinePartitionP k h * (2 * (k + 1) * uniformSchmidtP k + 4) ≤ _
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ ih

end LeanProofs.GowersSzemeredi
