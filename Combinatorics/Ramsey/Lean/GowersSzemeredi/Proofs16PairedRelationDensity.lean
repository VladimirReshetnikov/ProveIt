import GowersSzemeredi.Proofs16BohrDensityFactorization

/-! Independent relation classes for two varying blocks give the square of
the single-block density, with an explicit shared approximation error. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The weight of a product relation class factors exactly. -/
theorem latticeWeightMixed_product {N : Nat} [NeZero N] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (a : ι → Nat) (b : κ → Nat) (c R : Nat)
    (Lambda : Set (ι → centeredBall N R)) (Mu : Set (κ → centeredBall N R)) :
    latticeWeightMixed (Sum.elim a b) c R
      {v | (fun i => v (Sum.inl i)) ∈ Lambda ∧ (fun j => v (Sum.inr j)) ∈ Mu} =
      latticeWeightMixed a c R Lambda * latticeWeightMixed b c R Mu := by
  unfold latticeWeightMixed
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun v => (fun i => v (Sum.inl i), fun j => v (Sum.inr j)))
    (fun p => Sum.elim p.1 p.2) (by simp) (by simp)
    (fun v _ => by funext q; cases q <;> rfl) (fun p _ => rfl) (fun v _ => ?_)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Set.mem_setOf_eq]
  by_cases h1 : (fun i => v (Sum.inl i)) ∈ Lambda <;>
    by_cases h2 : (fun j => v (Sum.inr j)) ∈ Mu <;> simp [h1, h2]

/-- Squaring an approximate unit-interval density costs at most zeta(2+zeta). -/
theorem complex_square_near_density {w : Complex} {delta zeta : Real}
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (hw : ‖w - (delta : Complex)‖ ≤ zeta) :
    ‖w^2 - ((delta^2 : Real) : Complex)‖ ≤ zeta * (2 + zeta) := by
  have hz : 0 ≤ zeta := (norm_nonneg _).trans hw
  have hwn : ‖w‖ ≤ 1 + zeta := by
    have h := norm_sub_norm_le w (delta : Complex)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0] at h
    linarith
  have hsum : ‖w + (delta : Complex)‖ ≤ 2 + zeta := by
    have h := norm_add_le w (delta : Complex)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0] at h
    linarith
  have heq : w^2 - ((delta^2 : Real) : Complex) = (w - delta) * (w + delta) := by
    push_cast
    ring
  rw [heq, norm_mul]
  exact mul_le_mul hw hsum (norm_nonneg _) hz

/-- The paired relation class is close to the square of the same real density. -/
theorem paired_latticeWeightMixed_near_density {N : Nat} [NeZero N] {κ : Type*} [Fintype κ]
    (b : κ → Nat) (c R : Nat) (Lambda : Set (κ → centeredBall N R))
    {delta zeta : Real} (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hw : ‖latticeWeightMixed b c R Lambda - (delta : Complex)‖ ≤ zeta) :
    ‖latticeWeightMixed (Sum.elim b b) c R
        {v | (fun i => v (Sum.inl i)) ∈ Lambda ∧ (fun j => v (Sum.inr j)) ∈ Lambda} -
      ((delta^2 : Real) : Complex)‖ ≤ zeta * (2 + zeta) := by
  rw [latticeWeightMixed_product, ← sq]
  exact complex_square_near_density hd0 hd1 hw

end LeanProofs.GowersSzemeredi
