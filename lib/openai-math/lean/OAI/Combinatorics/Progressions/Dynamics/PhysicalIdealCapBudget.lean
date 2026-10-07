import OAI.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem physicalActiveProfileIdeal_exp_bound
    {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    (Z : Type*) {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    (R : D → ℝ) (hR : ∀ d, 0 < R d)
    {N p e : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e)
    (hcard : (Fintype.card (Σ d, O d) : ℝ) ≤ N)
    (hRi : ∀ d, (R d)⁻¹ ≤ Real.exp p)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (v : (Σ d, O d) → ℝ) :
    |physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v| ≤
      Real.exp (N * (p + e)) := by
  have hprod0 : 0 ≤ (∏ q : Σ d, O d, R q.1.val)⁻¹ :=
    inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val).le))
  have hprod : (∏ q : Σ d, O d, R q.1.val)⁻¹ ≤ Real.exp (N * p) := by
    calc
      _ = ‖(∏ q : Σ d, O d, R q.1.val)⁻¹‖ := (Real.norm_of_nonneg hprod0).symm
      _ ≤ Real.exp ((Fintype.card (Σ d, O d) : ℝ) * p) :=
        inverseProduct_norm_le_exp (fun q : Σ d, O d => R q.1.val)
          (fun q => (hR q.1.val).le) (fun q => hRi q.1.val)
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hp)
  have hnoise : ((δ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0) : ℝ) ≤ Real.exp (N * e) := by
    simp only [NNReal.coe_pow, NNReal.coe_inv]
    calc
      _ ≤ (Real.exp e) ^ Fintype.card (Σ d, O d) :=
        pow_le_pow_left₀ (inv_nonneg.mpr δ.coe_nonneg) hδe _
      _ = Real.exp ((Fintype.card (Σ d, O d) : ℝ) * e) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard he)
  calc
    _ ≤ _ := physicalActiveProfileIdeal_bound Z h P sets R hR δ hδ v
    _ ≤ Real.exp (N * p) * Real.exp (N * e) :=
      mul_le_mul hprod hnoise (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
