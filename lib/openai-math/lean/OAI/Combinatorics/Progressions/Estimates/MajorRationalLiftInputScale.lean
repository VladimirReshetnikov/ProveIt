import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def majorRationalLiftInputScale (d : ℕ) (p : ℝ) : ℝ :=
  ((d + 2 : ℕ) : ℝ) * (p + 1) + 8

theorem majorRationalLiftInputScale_bounds (d : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ majorRationalLiftInputScale d p ∧
      p ≤ majorRationalLiftInputScale d p ∧
      2 * p + 8 ≤ majorRationalLiftInputScale d p := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdp : 0 ≤ (d : ℝ) * p := mul_nonneg hd hp
  dsimp [majorRationalLiftInputScale]
  push_cast
  constructor
  · positivity
  constructor <;> nlinarith

theorem majorRationalLiftInputScale_mass (d : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (n m : ℕ) (hnm : ((n + m : ℕ) : ℝ) ≤ p) :
    ((n + m + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (majorRationalLiftInputScale d p) := by
  have hbase : ((n + m + 1 : ℕ) : ℝ) ≤ p + 1 := by
    push_cast at hnm ⊢
    linarith
  have hexp : p + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hscale : (d : ℝ) * (p + 1) ≤ majorRationalLiftInputScale d p := by
    dsimp [majorRationalLiftInputScale]
    push_cast
    nlinarith
  calc
    _ ≤ Real.exp (p + 1) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hbase.trans hexp) d
    _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hscale

end Erdos3

end

end OAI
