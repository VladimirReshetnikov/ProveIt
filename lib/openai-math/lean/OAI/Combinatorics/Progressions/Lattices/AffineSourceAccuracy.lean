import OAI.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy

namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

theorem affineSourceAccuracy_budget
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Dout Dgrid Prho Pbox Op E F C : ℝ}
    (hDout : 0 ≤ Dout) (hDgrid : 0 ≤ Dgrid) (hPrho : 0 ≤ Prho)
    (hPbox : 0 ≤ Pbox) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hout : (Fintype.card κ : ℝ) ≤ Dout) (hgrid : (Fintype.card ι : ℝ) ≤ Dgrid)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hC0 : 0 ≤ C) (hC : C ≤ Real.exp F) :
    let G := Dgrid * max Op 0
    let εgrid := Real.exp (-(Dout * Prho + (E + F) + 1))
    let εlong := Real.exp (-(G + (E + F) + 1))
    let Plong := Pbox + Prho + G + (E + F) + 2
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Dout * Prho + (E + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp Plong ∧
      0 ≤ Plong ∧ Pbox ≤ Plong ∧ (ρ : ℝ)⁻¹ ≤ Real.exp Plong ∧
      C * ((ρ⁻¹ ^ Fintype.card κ : ℝ≥0) * εgrid +
        εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-E) := by
  intro G εgrid εlong Plong
  have hG : 0 ≤ G := mul_nonneg hDgrid (le_max_right _ _)
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, herr⟩ :=
    slicedSourceAccuracy_bounds (mul_nonneg hDout hPrho) hG (add_nonneg hE hF)
  have hPlong : G + (E + F) + 1 ≤ Plong := by dsimp [Plong]; linarith
  have hb : Pbox ≤ Plong := by dsimp [Plong]; linarith
  have hr : Prho ≤ Plong := by dsimp [Plong]; linarith
  have hcap : (ρ⁻¹ ^ Fintype.card κ : ℝ≥0) ≤ Real.exp (Dout * Prho) := by
    rw [NNReal.coe_pow, NNReal.coe_inv]
    calc
      _ ≤ (Real.exp Prho) ^ Fintype.card κ := pow_le_pow_left₀ (inv_nonneg.mpr ρ.coe_nonneg) hρ _
      _ = Real.exp (Fintype.card κ * Prho) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hout hPrho)
  have hprod : (∏ _i : ι, Real.exp Op) ≤ Real.exp G := by
    simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hgrid (le_max_right _ _))
  refine ⟨hg0, hg1, hgi, hl0, hl1, hli.trans_le (Real.exp_le_exp.mpr hPlong),
    hPbox.trans hb, hb, hρ.trans (Real.exp_le_exp.mpr hr), ?_⟩
  calc
    _ ≤ C * (Real.exp (Dout * Prho) * εgrid + εlong * ∏ _i : ι, Real.exp Op) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact add_le_add (mul_le_mul_of_nonneg_right hcap hg0.le) le_rfl
    _ ≤ C * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_left (herr _ hprod) hC0
    _ ≤ Real.exp F * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
