import OAI.Combinatorics.Progressions.Dynamics.ComparableScalarSelectedBudget

namespace OAI

section

namespace Erdos3

theorem canonicalScalarFamily_error_le (d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    Real.exp (-(8 * ((d : ℝ)+1) * (p+1))) ≤ Real.exp (-p) :=
  Real.exp_le_exp.mpr (neg_le_neg (canonicalScalarTarget_dimension_bounds d hp).1)

theorem canonicalScalarFamilyMass (d cardFamily : ℕ) {p mass : ℝ}
    (hp : 0 ≤ p) (hcard : (cardFamily : ℝ) ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ mass) :
    let target := 8 * ((d : ℝ)+1) * (p+1)
    (cardFamily : ℝ) * Real.exp (-target) < mass := by
  intro target
  have htarget : 2*p < target := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hdp := mul_nonneg hd hp
    dsimp [target]
    nlinarith
  calc
    _ ≤ Real.exp p * Real.exp (-target) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = Real.exp (p-target) := by rw [← Real.exp_add, sub_eq_add_neg]
    _ < Real.exp (-p) := Real.exp_lt_exp.mpr (by linarith)
    _ ≤ mass := hmass

end Erdos3

end

end OAI
