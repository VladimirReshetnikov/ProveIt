import GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteLocalRules
import GRHArticle.ProgressionFree.NumberFieldIdeals.SquareNormTail
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Positive Euler products for ideal exponent rules

Allowing exponents zero and one loses at most the inverse squared norm
at each prime. Finitely many exceptional rules may be chosen arbitrarily
provided their individual masses are positive.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors Classical

variable {K : Type*} [Field K] [NumberField K]

theorem localRuleMass_mem_unitInterval (p : HeightOneSpectrum (𝓞 K)) (A : Set ℕ) :
    0 ≤ localRuleMass p A ∧ localRuleMass p A ≤ 1 := by
  obtain ⟨hw,hlt⟩ := primeWeight_pos_lt_one p
  have hs := (hasSum_geometric_of_lt_one hw.le hlt).summable
  have hpos n : 0 ≤ A.indicator (fun k ↦ primeWeight p^k) n :=
    Set.indicator_nonneg (fun i _ ↦ pow_nonneg hw.le i) n
  have hle' (n : ℕ) : A.indicator (fun k ↦ primeWeight p^k) n ≤ primeWeight p^n := by
    by_cases hn : n ∈ A
    · rw [Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hn]
      exact pow_nonneg hw.le _
  have hle := (hs.indicator A).tsum_le_tsum hle' hs
  rw [(hasSum_geometric_of_lt_one hw.le hlt).tsum_eq] at hle
  refine ⟨mul_nonneg (sub_nonneg.mpr hlt.le) (tsum_nonneg hpos),?_⟩
  exact (mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hlt.le)).trans_eq
    (mul_inv_cancel₀ (sub_pos.mpr hlt).ne')

theorem localRuleMass_pos_of_zero_mem (p : HeightOneSpectrum (𝓞 K)) {A : Set ℕ} (hA : 0 ∈ A) :
    0 < localRuleMass p A := by
  obtain ⟨hw,hlt⟩ := primeWeight_pos_lt_one p
  have hs := (summable_geometric_of_lt_one hw.le hlt).indicator A
  apply mul_pos (sub_pos.mpr hlt)
  apply lt_of_lt_of_le _ (hs.le_tsum (0:ℕ) (fun n _ ↦ Set.indicator_nonneg (fun i _ ↦ pow_nonneg hw.le i) n))
  simp [hA]

theorem one_sub_localRuleMass_le_sq (p : HeightOneSpectrum (𝓞 K)) {A : Set ℕ}
    (h0 : 0 ∈ A) (h1 : 1 ∈ A) : 1-localRuleMass p A ≤ primeWeight p^2 := by
  obtain ⟨hw,hlt⟩ := primeWeight_pos_lt_one p
  have hs := (summable_geometric_of_lt_one hw.le hlt).indicator A
  have h := hs.sum_le_tsum ({0,1}:Finset ℕ)
    (fun n _ ↦ Set.indicator_nonneg (fun i _ ↦ pow_nonneg hw.le i) n)
  simp [h0,h1] at h
  have hmul := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hlt.le)
  unfold localRuleMass
  linarith only [hmul,show (1-primeWeight p)*(1+primeWeight p) = 1-primeWeight p^2 by ring]

/-- The product of local probabilities converges and is strictly positive. -/
theorem localRuleEulerProductOn {ι : Type*} (v : ι → HeightOneSpectrum (𝓞 K))
    (hv : Function.Injective v) (S : Finset ι)
    (A : ι → Set ℕ) (h0 : ∀ p, 0 ∈ A p)
    (h1 : ∀ p ∉ S, 1 ∈ A p) :
    Multipliable (fun p ↦ localRuleMass (v p) (A p)) ∧ 0 < ∏' p, localRuleMass (v p) (A p) := by
  let f (p : ι) := localRuleMass (v p) (A p) - 1
  have hs : Summable fun p ↦ ‖f p‖ := by
    apply ((summable_primeIdeal_inv_sq_absNorm (K := K)).comp_injective hv).of_norm_bounded_eventually
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with p hp
    have h := (localRuleMass_mem_unitInterval (v p) (A p)).2
    simp only [Real.norm_eq_abs,f,abs_of_nonpos (sub_nonpos.mpr h),neg_sub,abs_of_nonneg (sub_nonneg.mpr h)]
    simpa only [primeWeight, inv_pow,Function.comp_apply] using one_sub_localRuleMass_le_sq (v p) (h0 p) (h1 p hp)
  have hpos (p) : 0 < 1+f p := by
    simpa [f] using localRuleMass_pos_of_zero_mem (v p) (h0 p)
  have hm := multipliable_one_add_of_summable hs
  have hne := tprod_one_add_ne_zero_of_summable (fun p ↦ (hpos p).ne') hs
  have hnon : 0 ≤ ∏' p, (1+f p) := ge_of_tendsto hm.hasProd (Eventually.of_forall
    fun t ↦ prod_nonneg (fun p _ ↦ (hpos p).le))
  simpa [f] using And.intro hm (lt_of_le_of_ne hnon hne.symm)

/-- The product of local probabilities converges and is strictly positive. -/
theorem localRuleEulerProduct (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : HeightOneSpectrum (𝓞 K) → Set ℕ) (h0 : ∀ p, 0 ∈ A p)
    (h1 : ∀ p ∉ S, 1 ∈ A p) :
    Multipliable (fun p ↦ localRuleMass p (A p)) ∧ 0 < ∏' p, localRuleMass p (A p) :=
  localRuleEulerProductOn id Function.injective_id S A h0 h1

end GRHArticle.ProgressionFree.NumberFieldIdeals
