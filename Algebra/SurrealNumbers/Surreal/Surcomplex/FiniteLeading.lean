import Surreal.Surcomplex.Leading

/-!
# Leading coefficients of finite actual surcomplex sums

A unique term of least valuation determines the leading coefficient of
a finite sum in the actual surcomplex field. In particular, finite sums
of distinct real-axis monomials have their expected complex leading
coefficients. No infinite Hahn evaluation is used.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A higher-valuation summand cannot change the leading coefficient. -/
theorem leadingCoeff_add_of_valuation_lt {x y : Surcomplex.{u}}
    (h : valuation x < valuation y) : leadingCoeff (x + y) = leadingCoeff x := by
  have hx : x ≠ 0 := by
    intro hx
    simp [hx] at h
  have hv : valuation (x + y) = valuation x := by
    rw [valuation_add_of_ne h.ne, min_eq_left h.le]
  have hxy : x + y ≠ 0 := by
    intro hxy
    have : valuation x = ⊤ := by simpa [hxy] using hv.symm
    exact hx ((valuation_eq_top_iff x).mp this)
  have he : leadingExponent (x + y) = leadingExponent x := by
    apply neg_injective
    apply WithTop.coe_injective
    simpa only [valuation_of_ne_zero hxy, valuation_of_ne_zero hx, leadingExponent] using hv
  have hi : IsInfinitesimal (y / tMonomial (-leadingExponent x)) :=
    (isInfinitesimal_div_tMonomial_iff _ _).mpr (by
      simpa only [valuation_of_ne_zero hx, leadingExponent] using h)
  have hn : normalized (x + y) = normalized x + y / tMonomial (-leadingExponent x) := by
    simp only [normalized, he, add_div]
  rw [leadingCoeff, hn, standardPart_add (finite_normalized x) (finite_of_infinitesimal hi),
    (standardPart_eq_zero_iff (finite_of_infinitesimal hi)).mpr hi, add_zero]
  rfl

@[simp] theorem leadingExponent_tMonomial (a : SignSequence.{u}) :
    leadingExponent (tMonomial a) = -a := by
  simp only [leadingExponent, modulus_tMonomial, SignSequence.tMonomial,
    SignSequence.leadingExponent_omegaPower]

@[simp] theorem leadingCoeff_tMonomial (a : SignSequence.{u}) :
    leadingCoeff (tMonomial a) = 1 := by
  simp only [leadingCoeff, normalized, leadingExponent_tMonomial, neg_neg,
    div_self (tMonomial_ne_zero a)]
  simpa only [map_one] using standardPart_ofComplex.{u} (1 : ℂ)

@[simp] theorem leadingCoeff_complex_mul_tMonomial (c : ℂ) (a : SignSequence.{u}) :
    leadingCoeff (ofComplex c * tMonomial a) = c := by
  rw [leadingCoeff_mul, leadingCoeff_ofComplex, leadingCoeff_tMonomial, mul_one]

/-- A unique finite-sum term of least valuation determines the sum's valuation. -/
theorem valuation_sum_eq_of_unique_min {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (f : ι → Surcomplex.{u}) (j : ι) (hj : j ∈ s)
    (hmin : ∀ i ∈ s, i ≠ j → valuation (f j) < valuation (f i)) :
    valuation (∑ i ∈ s, f i) = valuation (f j) := by
  apply (AddValuation.toValuation valuation).map_sum_eq_of_lt hj
  intro i hi
  obtain ⟨his, hij⟩ := Finset.mem_sdiff.mp hi
  exact hmin i his (by simpa only [Finset.mem_singleton] using hij)

/-- The unique least-valuation nonzero term determines the leading coefficient. -/
theorem leadingCoeff_sum_eq_of_unique_min {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (f : ι → Surcomplex.{u}) (j : ι) (hj : j ∈ s)
    (hj0 : f j ≠ 0) (hmin : ∀ i ∈ s, i ≠ j → valuation (f j) < valuation (f i)) :
    leadingCoeff (∑ i ∈ s, f i) = leadingCoeff (f j) := by
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  apply leadingCoeff_add_of_valuation_lt
  apply valuation.map_lt_sum ((valuation_eq_top_iff _).not.mpr hj0)
  intro i hi
  obtain ⟨his, hij⟩ := Finset.mem_sdiff.mp hi
  exact hmin i his (by simpa only [Finset.mem_singleton] using hij)

/-- A finite monomial sum has the coefficient at its unique least exponent
as its leading coefficient; the other coefficients may vanish. -/
theorem leading_finite_monomial_sum {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (a : ι → SignSequence.{u}) (c : ι → ℂ)
    (j : ι) (hj : j ∈ s) (hc : c j ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ j → a j < a i) :
    valuation (∑ i ∈ s, ofComplex (c i) * tMonomial (a i)) = ↑(a j) ∧
      leadingCoeff (∑ i ∈ s, ofComplex (c i) * tMonomial (a i)) = c j := by
  let f := fun i => ofComplex (c i) * tMonomial (a i)
  have hfv (i : ι) (hi : c i ≠ 0) : valuation (f i) = (a i : WithTop SignSequence.{u}) := by
    rw [valuation_mul, valuation_ofComplex hi, valuation_tMonomial, zero_add]
  have hjv := hfv j hc
  have hj0 : f j ≠ 0 := (valuation_eq_top_iff _).not.mp (by rw [hjv]; exact WithTop.coe_ne_top)
  have hv (i : ι) (hi : i ∈ s) (hij : i ≠ j) : valuation (f j) < valuation (f i) := by
    rw [hjv]
    by_cases hci : c i = 0
    · simp only [f, hci, map_zero, zero_mul, valuation_zero, WithTop.coe_lt_top]
    · rw [hfv i hci]
      exact WithTop.coe_lt_coe.mpr (hmin i hi hij)
  exact ⟨(valuation_sum_eq_of_unique_min s f j hj hv).trans hjv,
    (leadingCoeff_sum_eq_of_unique_min s f j hj hj0 hv).trans
      (leadingCoeff_complex_mul_tMonomial (c j) (a j))⟩

end

end Surreal.Surcomplex
