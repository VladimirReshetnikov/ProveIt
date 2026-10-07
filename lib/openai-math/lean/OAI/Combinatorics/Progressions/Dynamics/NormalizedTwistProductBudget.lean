import OAI.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion

namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {pw cw pv cv P : ℝ} {Lw Lv : ℝ≥0}

 theorem productUniform_exp_bounds
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv)
    (hP : 0 ≤ P) (hLw : (Lw : ℝ) ≤ Real.exp P) (hLv : (Lv : ℝ) ≤ Real.exp P)
    (hpw : pw ≤ Real.exp P) (hcw : cw ≤ Real.exp P)
    (hpv : pv ≤ Real.exp P) (hcv : cv ≤ Real.exp P) :
    ((Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
        Real.exp (2 * P + 1) ∧
      ((W.productUniform V).cover : ℝ) ≤ Real.exp (2 * P + 1) ∧
      ((W.productUniform V).modulus : ℝ) ≤ Real.exp (2 * P + 1) := by
  have hmax {c : ℝ} (hc : c ≤ Real.exp P) :
      ((max 1 (Real.toNNReal c) : ℝ≥0) : ℝ) ≤ Real.exp P := by
    simp only [NNReal.coe_max, NNReal.coe_one]
    exact max_le (Real.one_le_exp hP) (max_le hc (Real.exp_pos _).le)
  have hsum :
      ((Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
        2 * Real.exp (2 * P) := by
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul]
    have h1 := mul_le_mul hLw (hmax hcv)
      (NNReal.coe_nonneg (max 1 (Real.toNNReal cv))) (Real.exp_pos P).le
    have h2 := mul_le_mul hLv (hmax hcw)
      (NNReal.coe_nonneg (max 1 (Real.toNNReal cw))) (Real.exp_pos P).le
    have he : Real.exp P * Real.exp P = Real.exp (2 * P) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he] at h1 h2
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1; norm_num
  have hshift : 2 * Real.exp (2 * P) ≤ Real.exp (2 * P + 1) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmul {a b : ℕ} (ha : (a : ℝ) ≤ Real.exp P) (hb : (b : ℝ) ≤ Real.exp P) :
      ((a * b : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul ha hb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact ⟨hsum.trans hshift,
    hmul (W.cover_bound.trans hcw) (V.cover_bound.trans hcv),
    hmul (W.modulus_bound.trans hpw) (V.modulus_bound.trans hpv)⟩

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
