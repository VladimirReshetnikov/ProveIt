import OAI.Combinatorics.Progressions.Estimates.InvariantUnitFamily
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def symmetricUnitConstant (m : ℕ) : ℕ :=
  ⌈2 / momentLowerConstant m⌉₊ + m * m + 2 + (m + 1) * momentWeightBound m

noncomputable def symmetricUnitBudget (m : ℕ) (p : ℝ) : ℝ :=
  (2 * m + 2 : ℝ) * (p + 1) + symmetricUnitConstant m

theorem symmetricUnitBudget_bounds (m n : ℕ) (K : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    ((n ^ m * (m * m + 1) : ℕ) : ℝ) ≤ Real.exp (symmetricUnitBudget m p) ∧
      (symmetricUnitFamilyLip m n K : ℝ) ≤ Real.exp (symmetricUnitBudget m p) := by
  let D := ⌈2 / momentLowerConstant m⌉₊
  let B := momentWeightBound m
  have hc := momentLowerConstant_pos m
  have hnplus : (n + 1 : ℝ) ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hexp := Real.one_le_exp hp
    nlinarith
  have hnpow : (n : ℝ) ^ m ≤ Real.exp ((m : ℝ) * p) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg n) hn m
  have hnpowplus : (n + 1 : ℝ) ^ m ≤ Real.exp ((m : ℝ) * (p + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hnplus m
  have hd : 2 / momentLowerConstant m ≤ Real.exp D :=
    (Nat.le_ceil _).trans (by linarith [Real.add_one_le_exp (D : ℝ)])
  have hout : (n : ℝ) ^ m * (m * m + 1) + 1 ≤ Real.exp ((m : ℝ) * p + (m * m + 2)) := by
    rw [Real.exp_add]
    have hcoef : (m * m + 2 : ℝ) ≤ Real.exp (m * m + 2 : ℝ) := by
      linarith [Real.add_one_le_exp (m * m + 2 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hnpow (by positivity : (0 : ℝ) ≤ m * m + 1)
    have heone := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg m) hp)
    nlinarith
  have hradius : 2 / (symmetricEvaluationRadius m n : ℝ) ≤
      Real.exp ((D : ℝ) + m * (p + 1)) := by
    change 2 / (momentLowerConstant m / (n + 1 : ℝ) ^ m) ≤ _
    rw [Real.exp_add]
    calc
      _ = (2 / momentLowerConstant m) * (n + 1 : ℝ) ^ m := by field_simp
      _ ≤ _ := mul_le_mul hd hnpowplus (by positivity) (Real.exp_pos _).le
  have hB : (B : ℝ) ≤ Real.exp B := by linarith [Real.add_one_le_exp (B : ℝ)]
  have hBpow : (B : ℝ) ^ (m + 1) ≤ Real.exp ((m + 1 : ℝ) * B) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg B) hB (m + 1)
    rw [← Real.exp_nat_mul] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hraw : (symmetricEvaluationLip m K : ℝ) ≤
      Real.exp ((m : ℝ) + (m + 1) * B + p) := by
    change (m : ℝ) * ((B : ℝ) * K) * (B : ℝ) ^ m ≤ _
    rw [Real.exp_add, Real.exp_add]
    calc
      _ = (m : ℝ) * (B : ℝ) ^ (m + 1) * K := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul
        (by linarith [Real.add_one_le_exp (m : ℝ)]) hBpow (by positivity) (Real.exp_pos _).le)
        hK K.coe_nonneg (by positivity)
  have htotal : (symmetricUnitFamilyLip m n K : ℝ) ≤ Real.exp
      ((D : ℝ) + m * (p + 1) + (m * p + (m * m + 2)) + (m + (m + 1) * B + p)) := by
    change (2 / (symmetricEvaluationRadius m n : ℝ)) *
      (((n : ℝ) ^ m * (m * m + 1) + 1) * (symmetricEvaluationLip m K : ℝ)) ≤ _
    calc
      _ ≤ Real.exp ((D : ℝ) + m * (p + 1)) *
          (Real.exp (m * p + (m * m + 2)) * Real.exp (m + (m + 1) * B + p)) :=
        mul_le_mul hradius (mul_le_mul hout hraw (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbudget : (D : ℝ) + m * (p + 1) + (m * p + (m * m + 2)) +
      (m + (m + 1) * B + p) ≤ symmetricUnitBudget m p := by
    dsimp [symmetricUnitBudget, symmetricUnitConstant, D, B]
    push_cast
    nlinarith
  constructor
  · have hle : (m : ℝ) * p + (m * m + 2) ≤ symmetricUnitBudget m p := by
      dsimp [symmetricUnitBudget, symmetricUnitConstant]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) ⌈2 / momentLowerConstant m⌉₊,
        Nat.cast_nonneg (α := ℝ) (momentWeightBound m)]
    push_cast
    exact (le_add_of_nonneg_right zero_le_one).trans (hout.trans (Real.exp_le_exp.mpr hle))
  · exact htotal.trans (Real.exp_le_exp.mpr hbudget)

theorem exists_symmetricUnit_cost (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → symmetricUnitBudget m p ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := Polynomial.C (2 * m + 2) * (Polynomial.X + 1) +
    Polynomial.C (symmetricUnitConstant m)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, symmetricUnitBudget] using hbound p hp

end Erdos3

end

end OAI
