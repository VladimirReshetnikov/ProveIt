import GowersSzemeredi.Proofs16CubicExplicitExponent

/-! Remove the sampling ceiling from the cubic graph and slice controls.
These inequalities expose the polynomial dependence needed for comparison
with the manuscript's prescribed graph and width budgets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Rounding the sample count costs at most one additional Q/sigma. -/
theorem section16UniformSampleCount_le_seven {sigma theta gamma : Real} {k : Nat}
    (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (hQ : 1 ≤ section16Lemma9QBound sigma theta gamma k) :
    (section16UniformSampleCount sigma theta gamma k : Real) ≤
      7 * section16Lemma9QBound sigma theta gamma k / sigma := by
  have hQ0 := zero_lt_one.trans_le hQ
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 6 * section16Lemma9QBound sigma theta gamma k / sigma)).le
  have hone : 1 ≤ section16Lemma9QBound sigma theta gamma k / sigma :=
    (one_le_div hs).mpr (hs1.trans hQ)
  unfold section16UniformSampleCount
  rw [max_eq_right hQ]
  calc
    _ ≤ 6 * section16Lemma9QBound sigma theta gamma k / sigma + 1 := hceil
    _ ≤ 6 * section16Lemma9QBound sigma theta gamma k / sigma +
        section16Lemma9QBound sigma theta gamma k / sigma := add_le_add le_rfl hone
    _ = _ := by ring

/-- The graph count has no remaining ceiling and is quartic in Q/sigma. -/
theorem section16CubicLiftGraphBound_le_explicit {q k : Nat} {sigma theta gamma : Real}
    (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (hQ : 1 ≤ section16Lemma9QBound sigma theta gamma k) :
    section16CubicLiftGraphBound q k sigma theta gamma ≤
      9 * (7 * section16Lemma9QBound sigma theta gamma k / sigma)^4 * (q : Real)^2 := by
  unfold section16CubicLiftGraphBound
  gcongr
  exact section16UniformSampleCount_le_seven hs hs1 hQ

/-- The slice exponent loses only a fourth power of the explicit sample
budget, uniformly in the selected graph count. -/
theorem section16CubicSliceExponent_ge_explicit {q k : Nat} {sigma theta gamma : Real}
    (hq : 0 < q) (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (hQ : 1 ≤ section16Lemma9QBound sigma theta gamma k) :
    (2 : Real)^(-(27 : Real)) * sigma^3 /
        ((7 * section16Lemma9QBound sigma theta gamma k / sigma) * q)^4 ≤
      cubicBaseExponent (section16UniformSampleCount sigma theta gamma k * q) sigma := by
  have hR := section16UniformSampleCount_le_seven hs hs1 hQ
  have hRpos := section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k hs
  have hqreal : (0 : Real) < q := by exact_mod_cast hq
  have hRreal : (0 : Real) < section16UniformSampleCount sigma theta gamma k := by exact_mod_cast hRpos
  unfold cubicBaseExponent
  rw [Nat.cast_mul]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

end LeanProofs.GowersSzemeredi
