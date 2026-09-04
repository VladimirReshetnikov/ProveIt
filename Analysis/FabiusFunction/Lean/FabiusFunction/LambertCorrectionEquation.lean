import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The exact equation for the Lambert correction

The transseries volume's `q1:prop:B`.  Writing `u = 1/L`, the correction `v` to
the large-`z` inverse is characterised by `q = B(v,u)` with

`B(v,u) = 1/(1 - u v) - e^{-v} = ∑_{k ≥ 1} b_k(u) v^k`,  `b_k(u) = u^k - (-1)^k/k!`,

so that `B(0,u) = 0` and `∂_v B(0,u) = 1 + u`.  The content of the proposition
is that this is an *ordinary* analytic reversion at the origin, and the two
facts that make it one are exactly these: the value vanishes and the derivative
does not.

The module is deliberately independent of the rest of the corpus — it is a
statement about one explicit two-variable function — and it proves the
coefficient formula in a slightly stronger form than the volume states.  The
volume sums from `k = 1`; here the sum runs over all `k ≥ 0`, which is
legitimate because `b_0(u) = u^0 - (-1)^0/0! = 1 - 1 = 0`.  So the vanishing of
the constant term is not a side condition to be checked but a consequence of
the same formula, recorded as `corrCoeff_zero`.
-/

set_option autoImplicit false

open Filter

namespace Fabius

/-- `B(v,u) = 1/(1 - u v) - e^{-v}`, the exact equation satisfied by the
correction. -/
noncomputable def corrB (u v : ℝ) : ℝ := (1 - u * v)⁻¹ - Real.exp (-v)

/-- The coefficient `b_k(u) = u^k - (-1)^k / k!` of `v^k` in `B`. -/
noncomputable def corrCoeff (u : ℝ) (k : ℕ) : ℝ := u ^ k - (-1) ^ k / k.factorial

/-- `b_0(u) = 0`: the expansion has no constant term, for every `u`. -/
@[simp] theorem corrCoeff_zero (u : ℝ) : corrCoeff u 0 = 0 := by
  simp [corrCoeff]

/-- `b_1(u) = 1 + u`, the coefficient that makes the reversion ordinary. -/
@[simp] theorem corrCoeff_one (u : ℝ) : corrCoeff u 1 = 1 + u := by
  simp [corrCoeff]

/-- **`q1:prop:B`, first clause.**  `B(0,u) = 0`. -/
@[simp] theorem corrB_zero (u : ℝ) : corrB u 0 = 0 := by
  simp [corrB]

/-- The derivative of `B` in `v`, wherever the denominator does not vanish. -/
theorem hasDerivAt_corrB (u : ℝ) {v : ℝ} (h : 1 - u * v ≠ 0) :
    HasDerivAt (corrB u) (u / (1 - u * v) ^ 2 + Real.exp (-v)) v := by
  have hden : HasDerivAt (fun v : ℝ => 1 - u * v) (-u) v := by
    simpa using ((hasDerivAt_id v).const_mul u).const_sub 1
  have hinv : HasDerivAt (fun v : ℝ => (1 - u * v)⁻¹) (-(-u) / (1 - u * v) ^ 2) v :=
    hden.inv h
  have hexp : HasDerivAt (fun v : ℝ => Real.exp (-v)) (Real.exp (-v) * (-1)) v :=
    (hasDerivAt_neg v).exp
  have hsub := hinv.sub hexp
  simpa [corrB, neg_neg, sub_neg_eq_add] using hsub

/-- **`q1:prop:B`, second clause.**  `∂_v B(0,u) = 1 + u`. -/
theorem hasDerivAt_corrB_zero (u : ℝ) : HasDerivAt (corrB u) (1 + u) 0 := by
  have h := hasDerivAt_corrB u (v := 0) (by simp)
  have hval : u / (1 - u * 0) ^ 2 + Real.exp (-0) = 1 + u := by
    simp only [mul_zero, sub_zero, one_pow, div_one, neg_zero, Real.exp_zero]
    ring
  rwa [hval] at h

/-- The derivative at the origin is positive whenever `u ≥ 0`, which is the
whole reason the reversion is ordinary rather than singular. -/
theorem deriv_corrB_zero_pos {u : ℝ} (hu : 0 ≤ u) : 0 < 1 + u := by linarith

/-! ### The coefficient expansion -/

/-- The exponential series in the shape the expansion needs. -/
theorem summable_corrExpTerm (v : ℝ) :
    Summable fun k : ℕ => (-1) ^ k / k.factorial * v ^ k := by
  refine (Real.summable_pow_div_factorial (-v)).congr fun k => ?_
  rw [neg_pow]
  ring

theorem tsum_corrExpTerm (v : ℝ) :
    ∑' k : ℕ, (-1) ^ k / k.factorial * v ^ k = Real.exp (-v) := by
  have hexp : Real.exp (-v) = ∑' k : ℕ, (-v) ^ k / k.factorial := by
    simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp]
  refine tsum_congr fun k => ?_
  rw [neg_pow]
  ring

/-- **`q1:eq:Bvu`.**  The coefficient expansion of `B`, valid for `|u v| < 1`.
The sum runs over every `k ≥ 0`; the `k = 0` term is `b_0(u) = 0`, so this is
the volume's sum from `k = 1` with one redundant vanishing term. -/
theorem corrB_eq_tsum {u v : ℝ} (h : |u * v| < 1) :
    corrB u v = ∑' k : ℕ, corrCoeff u k * v ^ k := by
  have hnorm : ‖u * v‖ < 1 := by simpa using h
  have hs1 : Summable fun k : ℕ => u ^ k * v ^ k := by
    refine (summable_geometric_of_norm_lt_one hnorm).congr fun k => ?_
    rw [mul_pow]
  have hs2 := summable_corrExpTerm v
  have hgeom : ∑' k : ℕ, u ^ k * v ^ k = (1 - u * v)⁻¹ := by
    rw [tsum_congr fun k => (mul_pow u v k).symm, tsum_geometric_of_norm_lt_one hnorm]
  rw [corrB, ← hgeom, ← tsum_corrExpTerm v, ← Summable.tsum_sub hs1 hs2]
  refine tsum_congr fun k => ?_
  rw [corrCoeff]
  ring

end Fabius
