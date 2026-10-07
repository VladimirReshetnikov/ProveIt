import OAI.Combinatorics.Progressions.Estimates.MixedRootLosses

namespace OAI

section

namespace Erdos3

def mixedCyclicErrorSlope (s : ℕ) : ℕ := mixedRootTensorExponent s + mixedRootCornerExponent s

def mixedCyclicErrorBuffer (s : ℕ) : ℕ := 2 * mixedRootCornerCoefficient s + 14

theorem mixed_cyclic_error_bound (s : ℕ) {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + mixedCyclicErrorBuffer s) ≤ N) :
    (d ^ mixedRootTensorExponent s + 1) *
        ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s *
          Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s))) +
      12 * Real.exp (-(e + mixedCyclicErrorBuffer s)) + 2 / N ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have hn : d ^ mixedRootTensorExponent s + 1 ≤
      2 * Real.exp ((mixedRootTensorExponent s : ℝ) * u) := by
    have h := hp (mixedRootTensorExponent s)
    linarith [Real.one_le_exp (show 0 ≤ (mixedRootTensorExponent s : ℝ) * u by positivity)]
  have hcoef : (d ^ mixedRootTensorExponent s + 1) *
      ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s) ≤
      (2 * mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedCyclicErrorSlope s : ℝ) * u) := by
    calc
      _ ≤ (2 * Real.exp ((mixedRootTensorExponent s : ℝ) * u)) *
          ((mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedRootCornerExponent s : ℝ) * u)) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (hp (mixedRootCornerExponent s)) (Nat.cast_nonneg _))
          (by positivity) (by positivity)
      _ = (2 * mixedRootCornerCoefficient s : ℝ) *
          Real.exp ((mixedRootTensorExponent s : ℝ) * u + (mixedRootCornerExponent s : ℝ) * u) := by
        rw [Real.exp_add]
        ring
      _ = _ := by simp only [mixedCyclicErrorSlope, Nat.cast_add, add_mul]
  have hfirst : (d ^ mixedRootTensorExponent s + 1) *
      ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s *
        Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s))) ≤
      (2 * mixedRootCornerCoefficient s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    calc
      _ = ((d ^ mixedRootTensorExponent s + 1) *
          ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s)) *
            Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s)) := by ring
      _ ≤ ((2 * mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedCyclicErrorSlope s : ℝ) * u)) *
          Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using h
  have hthird : 2 / N ≤ 2 * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    calc
      _ = 2 * (1 / N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  calc
    _ ≤ (mixedCyclicErrorBuffer s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
      have h := add_le_add (add_le_add hfirst (le_refl (12 * Real.exp (-(e + mixedCyclicErrorBuffer s))))) hthird
      apply h.trans_eq
      have hB : (mixedCyclicErrorBuffer s : ℝ) = 2 * mixedRootCornerCoefficient s + 14 := by
        simp only [mixedCyclicErrorBuffer, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [hB]
      ring
    _ ≤ Real.exp (mixedCyclicErrorBuffer s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (mixedCyclicErrorBuffer s : ℝ)])
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
