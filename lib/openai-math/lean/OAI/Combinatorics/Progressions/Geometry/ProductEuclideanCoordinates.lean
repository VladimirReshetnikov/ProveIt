import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Pi

namespace OAI

section

namespace Erdos3

theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => ‖x i‖) (fun i _ => norm_nonneg (x i))
  have he := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (x i))
  have h : ‖x‖ ≤ ∑ i, ‖x i‖ := by nlinarith [norm_nonneg x]
  simpa only [Real.norm_eq_abs] using h

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def productEuclideanEquiv :
    ((σ → ℝ) × (κ → ℝ)) ≃ₗ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) :=
  (LinearEquiv.sumArrowLequivProdArrow σ κ ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (σ ⊕ κ) ℝ).symm.toLinearEquiv

omit [Fintype σ] [Fintype κ] in
@[simp] theorem productEuclideanEquiv_apply_inl (x : (σ → ℝ) × (κ → ℝ)) (i : σ) :
    productEuclideanEquiv x (Sum.inl i) = x.1 i := rfl

omit [Fintype σ] [Fintype κ] in
@[simp] theorem productEuclideanEquiv_apply_inr (x : (σ → ℝ) × (κ → ℝ)) (j : κ) :
    productEuclideanEquiv x (Sum.inr j) = x.2 j := rfl

theorem productEuclideanEquiv_norm_le (x : (σ → ℝ) × (κ → ℝ)) :
    ‖productEuclideanEquiv x‖ ≤ ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * ‖x‖ := by
  calc
    _ ≤ ∑ i : σ ⊕ κ, |productEuclideanEquiv x i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : σ ⊕ κ, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      cases i with
      | inl i =>
        simpa only [productEuclideanEquiv_apply_inl, ← Real.norm_eq_abs] using
          (norm_le_pi_norm x.1 i).trans (norm_fst_le x)
      | inr j =>
        simpa only [productEuclideanEquiv_apply_inr, ← Real.norm_eq_abs] using
          (norm_le_pi_norm x.2 j).trans (norm_snd_le x)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, nsmul_eq_mul]

theorem norm_le_productEuclideanEquiv (x : (σ → ℝ) × (κ → ℝ)) :
    ‖x‖ ≤ ‖productEuclideanEquiv x‖ := by
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact PiLp.norm_apply_le (productEuclideanEquiv x) (Sum.inl i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact PiLp.norm_apply_le (productEuclideanEquiv x) (Sum.inr j)

end Erdos3

end

end OAI
