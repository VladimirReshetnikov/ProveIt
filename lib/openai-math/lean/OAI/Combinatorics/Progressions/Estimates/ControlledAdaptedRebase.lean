import OAI.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_controlled_adapted_rebase :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (F : D.AdaptedModelData) (H : ℕ)
        (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H),
        p ≤ (p + C) ^ C ∧ F.model.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ {σ : Type*} {w : σ → ℕ} (T : D.Niltest w), T.ComplexityLE p →
          (F.rebaseNiltest H hH T).ComplexityLE ((p + C) ^ C)) ∧
        ∀ eta : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (eta (D.basis i)) ≤ p) →
          ∀ j, rationalLogHeight (eta (F.model.basis j)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + 2) ^ 2 + (X + 3) ^ 4 + X)
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D p hp hD
  obtain ⟨F, hF, hb⟩ := D.exists_adapted_model_data hp hD
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let r := (p + 3) ^ 11 + p + 2
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hfr : (p + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hHbound : (H : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [r]; linarith))
  have hr : 0 ≤ r := hp.trans hpr
  have hbud : r + (r + 2) ^ 2 + (p + 3) ^ 4 + p ≤ (p + C) ^ C := by
    simpa [R, X, r, Polynomial.eval₂_pow] using hbudget p hp
  have hfreq0 : 0 ≤ (p + 3) ^ 4 := by positivity
  have hcomp : r + (r + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hfreq : (p + 3) ^ 4 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hbase : p ≤ (p + C) ^ C := hpr.trans ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp)
  have hgeom : F.model.GeometryComplexityLE r := hF.mono F.model hfr
  refine ⟨F, H, hH, hbase, hgeom.mono F.model
    ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp), ?_, ?_⟩
  · intro σ w T hT
    exact (F.rebaseNiltest_complexity H hH T hr (hT.mono hpr) hgeom hHbound).mono hcomp
  · intro eta heta j
    have hdim : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
      simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
    have hval := rational_functional_value_logHeight D.basis eta
      (by linarith : 0 ≤ p + 1) hdim (fun i => (heta i).trans (by linarith : p ≤ p + 1))
      (F.basis j) (hb j)
    apply le_trans _ hfreq
    change rationalLogHeight (eta (F.basis j)) ≤ (p + 3) ^ 4
    simpa only [show p + 1 + 2 = p + 3 by ring] using hval

end Erdos3.RationalFilteredNilmanifold

end

end OAI
