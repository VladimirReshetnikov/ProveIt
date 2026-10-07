import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def spatialOutputScale {N : Type*} [Fintype N]
    (L : ℕ) (ρ ξ : ℝ) (W : N → ℝ) : ℝ := 1+(L : ℝ)*ρ+(∑ n, W n)*ρ/ξ

theorem spatialOutputScale_spec {N : Type*} [Fintype N]
    {L : ℕ} (hL : 0 < L) {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 < ξ)
    (W : N → ℝ) (hW : ∀ n, 0 ≤ W n) :
    0 < spatialOutputScale L ρ ξ W ∧ 1 ≤ spatialOutputScale L ρ ξ W ∧
    ρ ≤ spatialOutputScale L ρ ξ W/L ∧
    ∀ n, W n*ρ ≤ ξ*spatialOutputScale L ρ ξ W := by
  have hs : 0 ≤ ∑ n, W n := Finset.sum_nonneg (fun n _ => hW n)
  have h1 : 1 ≤ spatialOutputScale L ρ ξ W := by
    unfold spatialOutputScale
    have ha : 0 ≤ (L : ℝ)*ρ := by positivity
    have hb : 0 ≤ (∑ n, W n)*ρ/ξ := by positivity
    linarith
  have hpart : (L : ℝ)*ρ ≤ spatialOutputScale L ρ ξ W := by
    unfold spatialOutputScale
    have hh : 0 ≤ (∑ n, W n)*ρ/ξ := by positivity
    linarith
  refine ⟨lt_of_lt_of_le zero_lt_one h1, h1, ?_, ?_⟩
  · apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
    nlinarith
  · intro n
    have hsum : W n ≤ ∑ j, W j := Finset.single_le_sum (fun j _ => hW j) (Finset.mem_univ n)
    have hrest : (∑ j, W j)*ρ/ξ ≤ spatialOutputScale L ρ ξ W := by
      unfold spatialOutputScale
      have hh : 0 ≤ (L : ℝ)*ρ := by positivity
      linarith
    have hh := (div_le_iff₀ hξ).mp hrest
    nlinarith [mul_le_mul_of_nonneg_right hsum hρ.le]

theorem spatialOutputScale_log_bound {N : Type*} [Fintype N]
    (L : ℕ) {ρ ξ P : ℝ} (hρ : 0 ≤ ρ) (hξ : 0 < ξ) (hP : 0 ≤ P)
    (W : N → ℝ) (hW0 : ∀ n, 0 ≤ W n) (hW : ∀ n, W n ≤ Real.exp P)
    (hL : (L : ℝ) ≤ Real.exp P) (hρP : ρ ≤ Real.exp P) (hξP : ξ⁻¹ ≤ Real.exp P) :
    spatialOutputScale L ρ ξ W ≤ Real.exp (Fintype.card N+3*P+3) := by
  have hs0 : 0 ≤ ∑ n, W n := Finset.sum_nonneg (fun n _ => hW0 n)
  have hs : (∑ n, W n) ≤ Real.exp (Fintype.card N+P) := by
    calc
      _ ≤ ∑ _n : N, Real.exp P := Finset.sum_le_sum (fun n _ => hW n)
      _ = (Fintype.card N : ℝ)*Real.exp P := by simp
      _ ≤ Real.exp (Fintype.card N : ℝ)*Real.exp P := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
      _ = _ := (Real.exp_add _ _).symm
  have ht : (∑ n, W n)*ρ/ξ ≤ Real.exp (Fintype.card N+3*P) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp (Fintype.card N+P)*Real.exp P*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hl : (L : ℝ)*ρ ≤ Real.exp (Fintype.card N+3*P) := by
    calc
      _ ≤ Real.exp P*Real.exp P := mul_le_mul hL hρP hρ (Real.exp_pos _).le
      _ = Real.exp (2*P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card N)])
  have hone : 1 ≤ Real.exp (Fintype.card N+3*P) := Real.one_le_exp_iff.mpr (by positivity)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 3*Real.exp (Fintype.card N+3*P) := by unfold spatialOutputScale; linarith
    _ ≤ Real.exp 3*Real.exp (Fintype.card N+3*P) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
