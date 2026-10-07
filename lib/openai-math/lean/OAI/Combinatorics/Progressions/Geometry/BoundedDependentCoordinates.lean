import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3

open Module

noncomputable def dependentCoordinateBudget (p : ℝ) : ℝ :=
  preimageBasisBudget (p + sparseGeneratorBudget (4 * p + 1))

theorem dependentCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ dependentCoordinateBudget p := by
  apply preimageBasisBudget_nonneg
  exact add_nonneg hp (sparseGeneratorBudget_nonneg (by positivity))

theorem exists_dependent_coordinate_basis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ a k i, rationalLogHeight (v a k i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (fourDependentProjection J))) ℚ (fourDependentProjection J),
      ∀ a i, rationalLogHeight ((b a : ι → ℚ) i) ≤ dependentCoordinateBudget p := by
  classical
  let q := 4 * p + 1
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p + 1 ≤ q := by dsimp only [q]; linarith
  have hrows (S : Finset (Fin 4)) : (Fintype.card (Σ _ : S, ι) : ℝ) ≤ q := by
    have hS : Fintype.card S ≤ 4 := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using S.card_le_univ
    have hc : Fintype.card (Σ _ : S, ι) ≤ 4 * Fintype.card ι := by
      simpa using Nat.mul_le_mul_right (Fintype.card ι) hS
    calc
      _ ≤ (4 : ℝ) * Fintype.card ι := by exact_mod_cast hc
      _ ≤ 4 * p := mul_le_mul_of_nonneg_left hι (by norm_num)
      _ ≤ q := by dsimp only [q]; linarith
  have hκq : (Fintype.card κ : ℝ) ≤ q := hκ.trans ((by linarith : p ≤ p + 1).trans hpq)
  have hHq : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)
  obtain ⟨M, _, hM, u, hu, huH⟩ := exists_sparse_generators_exp_height J {1, 2} v hv
    (one_le_ceil_exp p) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    hq (hrows {1, 2}) hκq hHq
  obtain ⟨M', _, hM', u', hu', huH'⟩ := exists_sparse_generators_exp_height J {1, 3} v hv
    (one_le_ceil_exp p) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    hq (hrows {1, 3}) hκq hHq
  let t := p + sparseGeneratorBudget q
  have hpt : p ≤ t := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hq)
  have ht : 0 ≤ t := hp.trans hpt
  have huB (a : κ) (i : ι) : rationalLogHeight (u a i) ≤ t :=
    (rationalLogHeight_le_of_height (huH a i) hM).trans (le_add_of_nonneg_left hp)
  have huB' (a : κ) (i : ι) : rationalLogHeight (u' a i) ≤ t :=
    (rationalLogHeight_le_of_height (huH' a i) hM').trans (le_add_of_nonneg_left hp)
  obtain ⟨b, hb⟩ := exists_preimage_basis_logHeight (Pi.basisFun ℚ ι) (Pi.basisFun ℚ ι)
    (fourSparseFirstProjection J {1, 2}) (fourSparseFirstProjection J {1, 3})
    (LinearMap.id : (ι → ℚ) →ₗ[ℚ] (ι → ℚ)) u u' hu hu' ht
    (hι.trans hpt) (hκ.trans hpt) (hκ.trans hpt)
    (by simpa only [Pi.basisFun_repr] using huB)
    (by simpa only [Pi.basisFun_repr] using huB')
    (by simpa only [Pi.basisFun_repr, LinearMap.id_apply] using huB)
  change Basis (Fin (finrank ℚ (fourDependentProjection J))) ℚ (fourDependentProjection J) at b
  refine ⟨b, fun a i => ?_⟩
  exact hb a i

end Erdos3

end

end OAI
