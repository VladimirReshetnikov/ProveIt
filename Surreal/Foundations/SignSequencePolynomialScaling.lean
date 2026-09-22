import Surreal.Foundations.SignSequenceMonomials
import Mathlib.Data.Finset.Max

/-!
# Finite coefficient normalization by an actual Conway monomial

This supplies a finite scaling prerequisite for the odd-degree-root argument
in Conway, *On Numbers and Games*, Chapter 3, Theorem 25. It concerns the
real-closedness obligation distinguished in `found:sub:realclosed` of the
foundations article. Taking a maximum of the finitely many weighted growth
exponents makes all scaled coefficients finite and retains at least one
nonzero real residue. This version uses proved Conway monomials and field
division of their exponents, without assuming positive roots of arbitrary
order, a Hahn normal-form equivalence, or real closedness.

No polynomial factor lifting or odd-degree-root existence is claimed here.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A positive integral weight converts the coefficient bound into a bound on its
growth exponent divided by that weight. -/
theorem finite_div_omegaPower_pow_iff {x : SignSequence.{u}} (hx : x ≠ 0)
    (n : ℕ) (hn : 0 < n) (γ : SignSequence.{u}) :
    IsFinite (x / (omegaPower γ) ^ n) ↔ leadingExponent x / n ≤ γ := by
  rw [← omegaPower_nat_mul, finite_div_omegaPower_iff hx,
    div_le_iff₀ (Nat.cast_pos.mpr hn)]
  rw [mul_comm γ]

/-- The maximal weighted exponent is exactly where the scaled residue is nonzero. -/
theorem standardPart_div_omegaPower_pow_ne_zero_iff {x : SignSequence.{u}} (hx : x ≠ 0)
    (n : ℕ) (hn : 0 < n) (γ : SignSequence.{u}) :
    standardPart (x / (omegaPower γ) ^ n) ≠ 0 ↔ leadingExponent x / n = γ := by
  rw [← omegaPower_nat_mul, standardPart_div_omegaPower_ne_zero_iff hx,
    div_eq_iff (Nat.cast_ne_zero.mpr hn.ne')]
  rw [mul_comm γ]

/-- Every finite, nonzero coefficient family with positive integer weights has
a common monomial scaling with finite coefficients and an attained nonzero residue. -/
theorem exists_monomial_normalization {ι : Type v} [Fintype ι]
    (a : ι → SignSequence.{u}) (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (ha : ∃ i, a i ≠ 0) :
    ∃ γ : SignSequence.{u},
      (∀ i, IsFinite (a i / (omegaPower γ) ^ n i)) ∧
      ∃ i, standardPart (a i / (omegaPower γ) ^ n i) ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.filter fun i => a i ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s (fun i => leadingExponent (a i) / n i) hs
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  refine ⟨leadingExponent (a j) / n j, ?_, j, ?_⟩
  · intro i
    obtain hi | hi := eq_or_ne (a i) 0
    · simp [hi]
    · apply (finite_div_omegaPower_pow_iff hi (n i) (hn i) _).mpr
      exact hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  · exact (standardPart_div_omegaPower_pow_ne_zero_iff haj (n j) (hn j) _).mpr rfl

/-- Finiteness alone also holds for the all-zero family and the empty index type. -/
theorem exists_monomial_finite_scaling {ι : Type v} [Fintype ι]
    (a : ι → SignSequence.{u}) (n : ι → ℕ) (hn : ∀ i, 0 < n i) :
    ∃ γ : SignSequence.{u}, ∀ i, IsFinite (a i / (omegaPower γ) ^ n i) := by
  classical
  by_cases ha : ∃ i, a i ≠ 0
  · obtain ⟨γ, hγ, _⟩ := exists_monomial_normalization a n hn ha
    exact ⟨γ, hγ⟩
  · refine ⟨0, fun i => ?_⟩
    have hi : a i = 0 := by
      by_contra hi
      exact ha ⟨i, hi⟩
    simp [hi]

/-- The common scale is a positive actual sign-field element. -/
theorem exists_pos_coefficient_scaling {ι : Type v} [Fintype ι]
    (a : ι → SignSequence.{u}) (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (ha : ∃ i, a i ≠ 0) :
    ∃ t : SignSequence.{u}, 0 < t ∧
      (∀ i, IsFinite (a i / t ^ n i)) ∧
      ∃ i, standardPart (a i / t ^ n i) ≠ 0 := by
  obtain ⟨γ, hγ, hres⟩ := exists_monomial_normalization a n hn ha
  exact ⟨omegaPower γ, omegaPower_pos γ, hγ, hres⟩

/-- The weights `n-j` used for the lower coefficients of a monic degree-`n`
polynomial are positive; one monomial normalizes them simultaneously. -/
theorem exists_lowerCoeff_monomial_normalization (n : ℕ)
    (a : Fin n → SignSequence.{u}) (ha : ∃ j, a j ≠ 0) :
    ∃ γ : SignSequence.{u},
      (∀ j, IsFinite (a j / (omegaPower γ) ^ (n - j.val))) ∧
      ∃ j, standardPart (a j / (omegaPower γ) ^ (n - j.val)) ≠ 0 :=
  exists_monomial_normalization a (fun j => n - j.val)
    (fun j => Nat.sub_pos_of_lt j.isLt) ha

end

end Surreal.Foundations.SignSequence
