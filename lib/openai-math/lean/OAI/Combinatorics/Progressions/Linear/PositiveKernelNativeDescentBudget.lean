import OAI.Combinatorics.Progressions.Estimates.NativePresentPivotQuotientModel

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def nativePresentPivotQuotientExponent : ℕ :=
  Classical.choose (exists_nativePresentPivotQuotient_budget.{0, 0, 0})

theorem nativePresentPivotQuotientExponent_ge_two :
    2 ≤ nativePresentPivotQuotientExponent :=
  (Classical.choose_spec (exists_nativePresentPivotQuotient_budget.{0, 0, 0})).1

private noncomputable def positiveKernelNativeDescentPolynomial (s : ℕ) : Polynomial ℕ :=
  let q := Polynomial.X + (Polynomial.X + 2) ^ nativePresentPivotQuotientExponent + 1
  q + (q + 2) ^ nativeInvariantFamilyDescentExponent s

noncomputable def positiveKernelNativeDescentExponent (s : ℕ) : ℕ :=
  Classical.choose
    (exists_natPolynomial_fixed_power_budget (positiveKernelNativeDescentPolynomial s))

theorem positiveKernelNativeDescentExponent_ge_two (s : ℕ) :
    2 ≤ positiveKernelNativeDescentExponent s :=
  (Classical.choose_spec
    (exists_natPolynomial_fixed_power_budget (positiveKernelNativeDescentPolynomial s))).1

theorem positiveKernelNativeDescentBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let pDesc := p + (p + 2) ^ nativePresentPivotQuotientExponent + 1
    p ≤ pDesc ∧ 0 ≤ pDesc ∧
      (p + 2) ^ nativePresentPivotQuotientExponent ≤ pDesc ∧
      pDesc ≤ (p + 2) ^ positiveKernelNativeDescentExponent s ∧
      (pDesc + 2) ^ nativeInvariantFamilyDescentExponent s ≤
        (p + 2) ^ positiveKernelNativeDescentExponent s := by
  dsimp only
  have hquotient : 0 ≤ (p + 2) ^ nativePresentPivotQuotientExponent := by positivity
  have hdesc : 0 ≤
      (p + (p + 2) ^ nativePresentPivotQuotientExponent + 1 + 2) ^
        nativeInvariantFamilyDescentExponent s := by positivity
  have hbudget :
      p + (p + 2) ^ nativePresentPivotQuotientExponent + 1 +
        (p + (p + 2) ^ nativePresentPivotQuotientExponent + 1 + 2) ^
          nativeInvariantFamilyDescentExponent s ≤
        (p + 2) ^ positiveKernelNativeDescentExponent s := by
    simpa [positiveKernelNativeDescentPolynomial, positiveKernelNativeDescentExponent,
      Polynomial.eval₂_pow] using
      (Classical.choose_spec
        (exists_natPolynomial_fixed_power_budget (positiveKernelNativeDescentPolynomial s))).2 p hp
  exact ⟨by linarith, by positivity, by linarith, by linarith, by linarith⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
