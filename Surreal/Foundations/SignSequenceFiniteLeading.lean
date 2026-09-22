import Surreal.Foundations.SignSequenceValuation

/-!
# Leading terms of finite normal forms in the actual sign field

Finite sums of distinct Conway monomials have the expected least valuation
and leading coefficient. These are finite-support prerequisites for
`found:eq:normalform`; no infinite Hahn sum or normal-form equivalence is
assumed. All arithmetic and order are those of the constructed sign field.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A nonzero ordinary real coefficient has valuation zero. -/
theorem valuation_ofReal_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    valuation (ofReal r : SignSequence.{u}) = 0 := by
  have h : (ofReal r : SignSequence.{u}) ≠ 0 := by
    intro h
    apply hr
    exact ofReal.injective (h.trans (map_zero ofReal).symm)
  rw [valuation_of_ne_zero h, leadingExponent_ofReal, neg_zero, WithTop.coe_zero]

/-- The valuation of a nonzero real multiple of a Conway monomial is its
specified exponent in the increasing `t` convention. -/
theorem valuation_real_mul_tMonomial {r : ℝ} (hr : r ≠ 0) (a : SignSequence.{u}) :
    valuation (ofReal r * tMonomial a) = (a : WithTop SignSequence.{u}) := by
  rw [valuation_mul, valuation_ofReal_of_ne_zero hr, valuation_tMonomial, _root_.zero_add]

@[simp] theorem leadingCoeff_real_mul_tMonomial (r : ℝ) (a : SignSequence.{u}) :
    leadingCoeff (ofReal r * tMonomial a) = r := by
  simp only [leadingCoeff_mul, leadingCoeff_ofReal, tMonomial,
    leadingCoeff_omegaPower, mul_one]

/-- Adding a term of strictly greater valuation preserves the leading
coefficient of the dominant term. -/
theorem leadingCoeff_add_of_valuation_lt {x y : SignSequence.{u}}
    (h : valuation x < valuation y) : leadingCoeff (x + y) = leadingCoeff x := by
  have hv := _root_.Surreal.vlt_def.mpr
    ((archimedeanClass_toSurreal_lt_iff x y).mpr ((valuation_lt_iff x y).mp h))
  simpa only [leadingCoeff, toSurreal_add] using _root_.Surreal.leadingCoeff_add_eq_left hv

/-- A unique finite-sum term of least valuation determines the sum's valuation. -/
theorem valuation_sum_eq_of_unique_min {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (f : ι → SignSequence.{u}) (j : ι) (hj : j ∈ s)
    (hmin : ∀ i ∈ s, i ≠ j → valuation (f j) < valuation (f i)) :
    valuation (∑ i ∈ s, f i) = valuation (f j) := by
  apply (AddValuation.toValuation valuation).map_sum_eq_of_lt hj
  intro i hi
  obtain ⟨his, hij⟩ := Finset.mem_sdiff.mp hi
  exact hmin i his (by simpa only [Finset.mem_singleton] using hij)

/-- The same unique least-valuation term determines the leading coefficient. -/
theorem leadingCoeff_sum_eq_of_unique_min {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (f : ι → SignSequence.{u}) (j : ι) (hj : j ∈ s)
    (hj0 : f j ≠ 0) (hmin : ∀ i ∈ s, i ≠ j → valuation (f j) < valuation (f i)) :
    leadingCoeff (∑ i ∈ s, f i) = leadingCoeff (f j) := by
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  apply leadingCoeff_add_of_valuation_lt
  apply valuation.map_lt_sum ((valuation_eq_top_iff _).not.mpr hj0)
  intro i hi
  obtain ⟨his, hij⟩ := Finset.mem_sdiff.mp hi
  exact hmin i his (by simpa only [Finset.mem_singleton] using hij)

/-- In a finite normal form, a nonzero coefficient at a strictly least
exponent determines both valuation and leading coefficient. Zero coefficients
at the other exponents are permitted. -/
theorem leading_finite_monomial_sum {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (a : ι → SignSequence.{u}) (c : ι → ℝ)
    (j : ι) (hj : j ∈ s) (hc : c j ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ j → a j < a i) :
    valuation (∑ i ∈ s, ofReal (c i) * tMonomial (a i)) = ↑(a j) ∧
      leadingCoeff (∑ i ∈ s, ofReal (c i) * tMonomial (a i)) = c j := by
  let f := fun i => ofReal (c i) * tMonomial (a i)
  have hjv : valuation (f j) = (a j : WithTop SignSequence.{u}) :=
    valuation_real_mul_tMonomial hc (a j)
  have hj0 : f j ≠ 0 := (valuation_eq_top_iff _).not.mp (by rw [hjv]; exact WithTop.coe_ne_top)
  have hv (i : ι) (hi : i ∈ s) (hij : i ≠ j) : valuation (f j) < valuation (f i) := by
    rw [hjv]
    by_cases hci : c i = 0
    · simp only [f, hci, map_zero, zero_mul, valuation_zero, WithTop.coe_lt_top]
    · rw [valuation_real_mul_tMonomial hci (a i)]
      exact WithTop.coe_lt_coe.mpr (hmin i hi hij)
  exact ⟨(valuation_sum_eq_of_unique_min s f j hj hv).trans hjv,
    (leadingCoeff_sum_eq_of_unique_min s f j hj hj0 hv).trans
      (leadingCoeff_real_mul_tMonomial (c j) (a j))⟩

end

end Surreal.Foundations.SignSequence
