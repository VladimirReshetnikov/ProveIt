import ExponentialIdentities.TwoBaseIntegerExponent.ZeroDensity
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Arbitrary-order forward differences and progression obstructions

This module proves an iterated mean-value theorem for Mathlib's forward-difference operator,
specializes it to arbitrary real powers, and derives the sharp candidate-progression
obstruction uniformly for every order `r ≥ 2`.
-/

open Set Finset Function
open fwdDiff

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-- The falling coefficient in the `r`-th derivative of `t ↦ t ^ α`. -/
def fallingRpowCoeff (α : ℝ) (r : ℕ) : ℝ :=
  ∏ k ∈ Finset.range r, (α - k)

@[simp] theorem fallingRpowCoeff_zero (α : ℝ) : fallingRpowCoeff α 0 = 1 := by
  simp [fallingRpowCoeff]

theorem fallingRpowCoeff_succ (α : ℝ) (r : ℕ) :
    fallingRpowCoeff α (r + 1) = fallingRpowCoeff α r * (α - r) := by
  simp [fallingRpowCoeff, Finset.prod_range_succ]

/-- The derivative tower for a real power. -/
def rpowDerivativeFamily (α : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  fallingRpowCoeff α r * x ^ (α - r)

theorem hasDerivAt_rpowDerivativeFamily (α : ℝ) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rpowDerivativeFamily α r)
      (rpowDerivativeFamily α (r + 1) x) x := by
  have hp := Real.hasDerivAt_rpow_const (x := x) (p := α - r) (Or.inl hx.ne')
  dsimp only [rpowDerivativeFamily]
  rw [fallingRpowCoeff_succ]
  push_cast
  convert hp.const_mul (fallingRpowCoeff α r) using 1
  · rfl
  · rfl
  · rfl
  · rw [show α - (r : ℝ) - 1 = α - ((r : ℝ) + 1) by ring]
    ring

/-- An iterated mean-value theorem for forward differences.  If `F (k + 1)` is the
derivative of `F k` on the positive half-line, then the `r`-th step-`h` forward difference
of `F 0` is `h ^ r * F r d` at some point strictly between the endpoints. -/
theorem exists_iterated_fwdDiff_eq_pow_mul
    (F : ℕ → ℝ → ℝ) (r : ℕ) (hr : 1 ≤ r)
    (x h : ℝ) (hx : 0 < x) (hh : 0 < h)
    (hderiv : ∀ k : ℕ, k < r → ∀ y : ℝ, 0 < y →
      HasDerivAt (F k) (F (k + 1) y) y) :
    ∃ d : ℝ, x < d ∧ d < x + (r : ℝ) * h ∧
      Δ_[h]^[r] (F 0) x = h ^ r * F r d := by
  induction r generalizing F x with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        have hcont : ContinuousOn (F 0) (Icc x (x + h)) := by
          intro y hy
          exact (hderiv 0 (by omega) y (hx.trans_le hy.1)).continuousAt.continuousWithinAt
        obtain ⟨d, hd, hdEq⟩ := exists_hasDerivAt_eq_slope (F 0) (F 1)
          (by linarith : x < x + h) hcont (by
            intro y hy
            exact hderiv 0 (by omega) y (hx.trans hy.1))
        refine ⟨d, hd.1, ?_, ?_⟩
        · simpa using hd.2
        · have hdEq' : F 1 d = (F 0 (x + h) - F 0 x) / h := by
            simpa only [add_sub_cancel_left] using hdEq
          have hslope : F 0 (x + h) - F 0 x = F 1 d * h :=
            ((eq_div_iff hh.ne').mp hdEq').symm
          simpa [fwdDiff, mul_comm] using hslope
      · have hrpos : 1 ≤ r := by omega
        let G : ℕ → ℝ → ℝ := fun k ↦ Δ_[h] (F k)
        have hGderiv : ∀ k : ℕ, k < r → ∀ y : ℝ, 0 < y →
            HasDerivAt (G k) (G (k + 1) y) y := by
          intro k hk y hy
          have houter := hderiv k (hk.trans (Nat.lt_succ_self r)) (y + h) (by positivity)
          have hshift : HasDerivAt (fun z : ℝ ↦ F k (z + h)) (F (k + 1) (y + h)) y :=
            houter.comp_add_const y h
          have hbase := hderiv k (hk.trans (Nat.lt_succ_self r)) y hy
          change HasDerivAt (fun z : ℝ ↦ F k (z + h) - F k z)
            (F (k + 1) (y + h) - F (k + 1) y) y
          convert hshift.sub hbase using 1 <;> rfl
        obtain ⟨c, hcx, hcupper, hcEq⟩ :=
          ih (F := G) hrpos x hx hGderiv
        have hcpos : 0 < c := hx.trans hcx
        have hcont : ContinuousOn (F r) (Icc c (c + h)) := by
          intro y hy
          exact (hderiv r (Nat.lt_succ_self r) y
            (hcpos.trans_le hy.1)).continuousAt.continuousWithinAt
        obtain ⟨d, hd, hdEq⟩ := exists_hasDerivAt_eq_slope (F r) (F (r + 1))
          (by linarith : c < c + h) hcont (by
            intro y hy
            exact hderiv r (Nat.lt_succ_self r) y (hcpos.trans hy.1))
        have hdEq' : F (r + 1) d = (F r (c + h) - F r c) / h := by
          simpa only [add_sub_cancel_left] using hdEq
        have hslope : F r (c + h) - F r c = F (r + 1) d * h :=
          ((eq_div_iff hh.ne').mp hdEq').symm
        refine ⟨d, hcx.trans hd.1, ?_, ?_⟩
        · have : d < x + (r : ℝ) * h + h := hd.2.trans_le (by linarith)
          push_cast
          linarith
        · rw [iterate_succ_apply]
          change Δ_[h]^[r] (G 0) x = _
          rw [hcEq]
          change h ^ r * (F r (c + h) - F r c) = _
          rw [hslope]
          ring

/-- Exact arbitrary-order mean-value identity for the forward differences of a real power. -/
theorem exists_iterated_fwdDiff_rpow_point
    (α x h : ℝ) (r : ℕ) (hr : 1 ≤ r) (hx : 0 < x) (hh : 0 < h) :
    ∃ d : ℝ, x < d ∧ d < x + (r : ℝ) * h ∧
      Δ_[h]^[r] (fun y : ℝ ↦ y ^ α) x =
        fallingRpowCoeff α r * h ^ r * d ^ (α - r) := by
  obtain ⟨d, hdx, hdupper, hdEq⟩ :=
    exists_iterated_fwdDiff_eq_pow_mul (rpowDerivativeFamily α) r hr x h hx hh
      (fun k _hk y hy ↦ hasDerivAt_rpowDerivativeFamily α k hy)
  have hFzero : rpowDerivativeFamily α 0 = (fun y : ℝ ↦ y ^ α) := by
    funext y
    simp [rpowDerivativeFamily, fallingRpowCoeff]
  rw [hFzero] at hdEq
  refine ⟨d, hdx, hdupper, ?_⟩
  simpa [rpowDerivativeFamily, fallingRpowCoeff, mul_assoc, mul_left_comm, mul_comm]
    using hdEq

/-- An iterated forward difference is integral whenever all values entering its binomial
expansion are integral. -/
theorem iterated_fwdDiff_mem_intCast_of_mem_intCast
    (f : ℝ → ℝ) (r : ℕ) (x h : ℝ)
    (hint : ∀ k : ℕ, k ≤ r →
      f (x + (k : ℝ) * h) ∈ Set.range ((↑) : ℤ → ℝ)) :
    Δ_[h]^[r] f x ∈ Set.range ((↑) : ℤ → ℝ) := by
  let S : Subring ℝ := (Int.castRingHom ℝ).range
  change Δ_[h]^[r] f x ∈ S
  rw [fwdDiff_iter_eq_sum_shift]
  apply S.sum_mem
  intro k hk
  apply S.zsmul_mem
  obtain ⟨z, hz⟩ := hint k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  refine ⟨z, ?_⟩
  simpa [nsmul_eq_mul] using hz

/-- None of the factors in the arbitrary-order derivative coefficient vanishes once the
order is at least two. -/
theorem fallingRpowCoeff_logThreeDivLogTwo_ne_zero
    (r : ℕ) :
    fallingRpowCoeff logThreeDivLogTwo r ≠ 0 := by
  rw [fallingRpowCoeff]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simpa using ne_of_gt (zero_lt_one.trans one_lt_logThreeDivLogTwo)
  by_cases hk1 : k = 1
  · subst k
    simpa using ne_of_gt (sub_pos.mpr one_lt_logThreeDivLogTwo)
  have hk2 : 2 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  linarith [logThreeDivLogTwo_lt_eight_fifths]

/-- Under the sharp arbitrary-order curvature inequality, the absolute forward difference
is strictly between zero and one. -/
theorem abs_iterated_fwdDiff_logThreeDivLogTwo_lt_one_of_curvature
    (r n h : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      |fallingRpowCoeff logThreeDivLogTwo r| * (h : ℝ) ^ r <
        (n : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo)) :
    0 < |Δ_[(h : ℝ)]^[r] (fun y : ℝ ↦ y ^ logThreeDivLogTwo) n| ∧
      |Δ_[(h : ℝ)]^[r] (fun y : ℝ ↦ y ^ logThreeDivLogTwo) n| < 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  obtain ⟨d, hdlo, _hdhi, hdEq⟩ :=
    exists_iterated_fwdDiff_rpow_point logThreeDivLogTwo n h r (by omega)
      hnpos hhpos
  have hdpos : 0 < d := hnpos.trans hdlo
  have hcoefne := fallingRpowCoeff_logThreeDivLogTwo_ne_zero r
  have hexpneg : logThreeDivLogTwo - (r : ℝ) < 0 := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hdiffne :
      Δ_[(h : ℝ)]^[r] (fun y : ℝ ↦ y ^ logThreeDivLogTwo) n ≠ 0 := by
    rw [hdEq]
    exact mul_ne_zero
      (mul_ne_zero hcoefne (pow_ne_zero _ hhpos.ne'))
      (ne_of_gt (Real.rpow_pos_of_pos hdpos _))
  have habsEq :
      |Δ_[(h : ℝ)]^[r] (fun y : ℝ ↦ y ^ logThreeDivLogTwo) n| =
        |fallingRpowCoeff logThreeDivLogTwo r| * (h : ℝ) ^ r *
          d ^ (logThreeDivLogTwo - (r : ℝ)) := by
    rw [hdEq, abs_mul, abs_mul, abs_of_pos (pow_pos hhpos r),
      abs_of_pos (Real.rpow_pos_of_pos hdpos _)]
  have hcoefpos :
      0 < |fallingRpowCoeff logThreeDivLogTwo r| * (h : ℝ) ^ r :=
    mul_pos (abs_pos.mpr hcoefne) (pow_pos hhpos r)
  have hpowlt : d ^ (logThreeDivLogTwo - (r : ℝ)) <
      (n : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) :=
    Real.rpow_lt_rpow_of_neg hnpos hdlo hexpneg
  have hpowpos : 0 < (n : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) :=
    Real.rpow_pos_of_pos hnpos _
  have hmul :
      |fallingRpowCoeff logThreeDivLogTwo r| * (h : ℝ) ^ r *
          (n : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) <
        (n : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) *
          (n : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) :=
    mul_lt_mul_of_pos_right hcurv hpowpos
  have hcancel :
      (n : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) *
          (n : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) = 1 := by
    rw [← Real.rpow_add hnpos]
    norm_num
  constructor
  · exact abs_pos.mpr hdiffne
  · rw [habsEq]
    exact (mul_lt_mul_of_pos_left hpowlt hcoefpos).trans
      (hmul.trans_eq hcancel)

/-- Under the sharp arbitrary-order curvature bound, `r + 1` integral power values cannot
occur at the arithmetic progression `n, n + h, ..., n + r * h`. -/
theorem not_arithmetic_progression_logThreeDivLogTwo_rpow_integers_of_curvature
    (r n h : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      |fallingRpowCoeff logThreeDivLogTwo r| * (h : ℝ) ^ r <
        (n : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo))
    (hint : ∀ k : ℕ, k ≤ r →
      ∃ z : ℤ, (z : ℝ) = ((n + k * h : ℕ) : ℝ) ^ logThreeDivLogTwo) :
    False := by
  obtain ⟨habspos, habslt⟩ :=
    abs_iterated_fwdDiff_logThreeDivLogTwo_lt_one_of_curvature
      r n h hr hn hh hcurv
  have hdint :
      Δ_[(h : ℝ)]^[r] (fun y : ℝ ↦ y ^ logThreeDivLogTwo) n ∈
        Set.range ((↑) : ℤ → ℝ) := by
    apply iterated_fwdDiff_mem_intCast_of_mem_intCast
    intro k hk
    obtain ⟨z, hz⟩ := hint k hk
    refine ⟨z, ?_⟩
    rw [hz]
    congr 1
    push_cast
    ring
  obtain ⟨z, hz⟩ := hdint
  have hzpos : (0 : ℤ) < |z| := by
    exact_mod_cast (show (0 : ℝ) < |(z : ℝ)| by
      rw [hz]
      exact habspos)
  have hzlt : |z| < (1 : ℤ) := by
    exact_mod_cast (show |(z : ℝ)| < (1 : ℝ) by
      rw [hz]
      exact habslt)
  omega

/-- Uniform arbitrary-order progression obstruction for natural two-base candidates. -/
theorem not_arithmetic_progression_twoBaseNaturalCandidates_of_curvature
    (r n h : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      |fallingRpowCoeff logThreeDivLogTwo r| * (h : ℝ) ^ r <
        (n : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo)) :
    ¬ ∀ k : ℕ, k ≤ r → TwoBaseNaturalCandidate (n + k * h) := by
  intro hcandidates
  apply not_arithmetic_progression_logThreeDivLogTwo_rpow_integers_of_curvature
    r n h hr hn hh hcurv
  intro k hk
  exact (hcandidates k hk).2

end

end LeanProofs.TwoBaseIntegerExponent
