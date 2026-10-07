import OAI.Combinatorics.Progressions.Polynomial.RefinementPolynomialBound

namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

theorem realBilinearAverage_le_of_cellBilinearBound
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {a : G → ℝ} {T : ℝ} (hT : 0 ≤ T) (hbound : CellBilinearBound Finset.univ a T)
    (f g : G → ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    realBilinearAverage a f g ≤ T := by
  have h := hbound 0 f g hf hg (by simp) (by simp)
  have hu : 0 ≤ 𝔼 r, f r := Finset.expect_nonneg (fun r _ => (hf r).1)
  have hv : 0 ≤ 𝔼 r, g r := Finset.expect_nonneg (fun r _ => (hg r).1)
  have hu1 : (𝔼 r, f r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ Finset.univ) => (hf r).2)).trans_eq
      (Finset.expect_const Finset.univ_nonempty 1)
  have hv1 : (𝔼 r, g r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ Finset.univ) => (hg r).2)).trans_eq
      (Finset.expect_const Finset.univ_nonempty 1)
  have hPhi : ((𝔼 r, f r) * (𝔼 r, g r)) ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one (mul_nonneg hu hv) (by nlinarith) (by norm_num)
  have h' := h.trans (mul_le_mul_of_nonneg_left hPhi hT)
  simpa only [zero_add, mul_one, realBilinearAverage, bilinearIntegral] using h'

theorem exists_degree_one_bilinear_bound {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p →
      ∀ A B : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} 1 N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) A B →
      ∀ f g : ZMod N → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      realBilinearAverage (fun r => A r - (1 + epsilon) * B r) f g ≤ Real.exp (-4 * p) := by
  obtain ⟨H, hH, hquant⟩ := exists_quantitative_bohr_bound hepsilon
  have hgap : 0 < 1 - refinementContraction epsilon := by
    linarith [(refinementContraction_bounds epsilon).2]
  have hinv : 0 ≤ 32 / (1 - refinementContraction epsilon) := by positivity
  obtain ⟨K, hK⟩ := exists_nat_ge (512 + 32 / (1 - refinementContraction epsilon))
  have hK512 : 512 ≤ K := by
    have h : (512 : ℝ) ≤ K := by linarith
    exact_mod_cast h
  have hKgap : 32 / (1 - refinementContraction epsilon) ≤ (K : ℝ) := by linarith
  obtain ⟨C, hC, hcost⟩ := exists_rescaled_refinement_budget hepsilon hH K
  refine ⟨C, hC, ?_⟩
  intro N hN p hp A B hA hB hcompare f g hf hg
  have hp0 : 0 ≤ p := by linarith
  let q := (K : ℝ) * (p + 1)
  obtain ⟨hq512, hpq, hKq⟩ := refinement_enlargement_bounds hp0 hK512
  have hqgap : 32 / (1 - refinementContraction epsilon) ≤ q := hKgap.trans hKq
  have hAq : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp q := fun r =>
    ⟨(hA r).1, (hA r).2.trans (Real.exp_le_exp.mpr hpq)⟩
  have hBq : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp q := fun r =>
    ⟨(hB r).1, (hB r).2.trans (Real.exp_le_exp.mpr hpq)⟩
  have hWcap : 2 * Real.exp p ≤ Real.exp (q / 8) :=
    refinement_enlargement_amplitude hp0 (by omega)
  have ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ 2 * Real.exp p := fun r =>
    signed_comparison_amplitude (hA r) (hB r) hepsilon.le hepsilon1.le
  have hcell := hquant N CyclicBohr.Set.whole q 0 ((p + 2) ^ C) (2 * Real.exp p)
    CyclicBohr.Set.isRankRegular_whole (by norm_num) (by norm_num) (by norm_num)
    hq512 hqgap (by norm_num) (by norm_num) A B hAq hBq (by positivity) hWcap ha hcompare
    (by simpa only [CyclicBohr.Set.rank_whole, zero_add] using hcost p hp0)
  have hwhole : CellBilinearBound Finset.univ (fun r => A r - (1 + epsilon) * B r)
      (2 * Real.exp (-q / 8)) := by
    simpa only [CyclicBohr.Set.carrier_whole] using hcell
  exact (realBilinearAverage_le_of_cellBilinearBound (by positivity) hwhole f g hf hg).trans
    (refinement_enlargement_error hp0 (by omega))

end Erdos3.CellRefinement

end

end OAI
