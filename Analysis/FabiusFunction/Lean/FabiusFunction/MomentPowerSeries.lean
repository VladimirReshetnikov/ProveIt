import FabiusFunction.Arithmetic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Formal power series for the Fabius moment sequences

This file proves, entirely in exact rational arithmetic, that the half moments
are the even-binomial transform of the moments.  The key step packages the
recurrence defining `moment` as a formal-power-series identity.  This avoids
using any analytic facts about the Fabius or Rvachev functions in the proof of
the inverse-power evaluator formula.  A single arbitrary-translation
coefficient calculation supplies both the centered-series API and the
half-translation used in the recurrence proof.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius

/-- Equation (9), the original recurrence before isolating `c_n`. -/
theorem moment_original_recurrence (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * n) * moment n =
      ∑ k ∈ range (n + 1),
        (Nat.choose (2 * n + 1) (2 * k) : ℚ) * moment k := by
  cases n with
  | zero => norm_num [moment]
  | succ n =>
      rw [sum_range_succ, moment_succ]
      rw [Fin.sum_univ_eq_sum_range
        (fun k =>
          (Nat.choose (2 * (n + 1) + 1) (2 * k) : ℚ) * moment k) (n + 1)]
      have hchoose : (2 * (n + 1) + 1).choose (2 * (n + 1)) =
          2 * (n + 1) + 1 := by
        exact Nat.choose_succ_self_right (2 * (n + 1))
      rw [hchoose]
      have hpow : (2 : ℚ) ^ (2 * (n + 1)) - 1 ≠ 0 := by
        apply ne_of_gt
        exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
      field_simp
      ring

/-- The generating series `∑ (moment n / (2 * n)!) * X ^ n` of the Fabius
moments. -/
noncomputable def momentPS : PowerSeries ℚ :=
  PowerSeries.mk fun n => moment n / ((2 * n).factorial : ℚ)

/-- The generating series `∑ X ^ n / (2 * n + 1)!`, obtained from `sinh x / x`
by substituting `X` for `x ^ 2`. -/
noncomputable def sinhDivPS : PowerSeries ℚ :=
  PowerSeries.mk fun n => 1 / ((2 * n + 1).factorial : ℚ)

/-- The original moment recurrence, packaged as the functional equation
`momentPS (4 * X) = momentPS * sinhDivPS` between formal power series. -/
lemma momentPS_functional :
    PowerSeries.rescale 4 momentPS = momentPS * sinhDivPS := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul]
  simp only [momentPS, sinhDivPS, PowerSeries.coeff_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hleft :
      (((2 * n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * n) * moment n) /
          ((2 * n + 1).factorial : ℚ) =
        4 ^ n * (moment n / ((2 * n).factorial : ℚ)) := by
    rw [show 2 * n + 1 = (2 * n).succ by omega, Nat.factorial_succ]
    norm_num [pow_mul]
    field_simp
  have hterm (x : ℕ) (hx : x ∈ range n.succ) :
      ((Nat.choose (2 * n + 1) (2 * x) : ℚ) * moment x) /
          ((2 * n + 1).factorial : ℚ) =
        moment x / ((2 * x).factorial : ℚ) *
          (1 / ((2 * (n - x) + 1).factorial : ℚ)) := by
    have hxle : 2 * x ≤ 2 * n + 1 := by
      have : x ≤ n := Nat.le_of_lt_succ (mem_range.1 hx)
      omega
    rw [Nat.cast_choose ℚ hxle]
    have hsub : 2 * n + 1 - 2 * x = 2 * (n - x) + 1 := by
      have : x ≤ n := Nat.le_of_lt_succ (mem_range.1 hx)
      omega
    rw [hsub]
    field_simp
  have h := congrArg
    (fun q : ℚ => q / ((2 * n + 1).factorial : ℚ))
    (moment_original_recurrence n)
  rw [hleft] at h
  rw [Finset.sum_div] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro x hx
  exact hterm x hx

private noncomputable def expm1DivPSQ : PowerSeries ℚ :=
  PowerSeries.mk fun n => 1 / ((n + 1).factorial : ℚ)

private lemma X_mul_expm1DivPSQ :
    (PowerSeries.X : PowerSeries ℚ) * expm1DivPSQ =
      PowerSeries.exp ℚ - 1 := by
  ext (_ | n)
  · simp
  · simp [expm1DivPSQ, PowerSeries.coeff_exp]

private noncomputable def expandedSinhDivPS : PowerSeries ℚ :=
  PowerSeries.expand 2 (by omega) (PowerSeries.rescale (1 / 4) sinhDivPS)

private lemma X_mul_expandedSinhDivPS :
    (PowerSeries.X : PowerSeries ℚ) * expandedSinhDivPS =
      PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) -
        PowerSeries.rescale (-1 / 2) (PowerSeries.exp ℚ) := by
  ext (_ | m)
  · rw [PowerSeries.coeff_zero_X_mul]
    simp only [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    norm_num
  · simp only [PowerSeries.coeff_succ_X_mul, expandedSinhDivPS,
      PowerSeries.coeff_expand, PowerSeries.coeff_rescale, sinhDivPS,
      PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_exp]
    rcases m.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← two_mul k]
      simp
      norm_num [pow_succ, pow_mul, div_pow]
      ring
    · have hnot : ¬ 2 ∣ 2 * k + 1 := Nat.not_two_dvd_bit1 k
      rw [if_neg hnot]
      norm_num [pow_succ, pow_mul]

private lemma expm1DivPSQ_mul_exp_half :
    expm1DivPSQ * PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) =
      PowerSeries.exp ℚ * expandedSinhDivPS := by
  apply PowerSeries.X_pow_mul_cancel (k := 1)
  simp only [pow_one]
  rw [← mul_assoc, X_mul_expm1DivPSQ]
  calc
    (PowerSeries.exp ℚ - 1) *
          PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) =
        PowerSeries.exp ℚ *
            PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) -
          PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) := by ring
    _ = PowerSeries.exp ℚ *
        (PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) -
          PowerSeries.rescale (-1 / 2) (PowerSeries.exp ℚ)) := by
      have h : PowerSeries.exp ℚ *
          PowerSeries.rescale (-1 / 2) (PowerSeries.exp ℚ) =
            PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) := by
        convert
          (PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) (1 : ℚ) (-1 / 2))
            using 1 <;> norm_num
      rw [mul_sub, h]
    _ = (PowerSeries.X : PowerSeries ℚ) *
        (PowerSeries.exp ℚ * expandedSinhDivPS) := by
      rw [← X_mul_expandedSinhDivPS]
      ring

private noncomputable def expandedMomentQuarter : PowerSeries ℚ :=
  PowerSeries.expand 2 (by omega) (PowerSeries.rescale (1 / 4) momentPS)

private lemma rescale_two_expandedMomentQuarter :
    PowerSeries.rescale 2 expandedMomentQuarter =
      PowerSeries.expand 2 (by omega) momentPS := by
  ext m
  simp only [PowerSeries.coeff_rescale, expandedMomentQuarter,
    PowerSeries.coeff_expand]
  split_ifs with hm
  · obtain ⟨k, rfl⟩ := hm
    norm_num [pow_mul, div_pow]
  · simp

private lemma expandedSinhDivPS_mul_expandedMomentQuarter :
    expandedSinhDivPS * expandedMomentQuarter =
      PowerSeries.expand 2 (by omega) momentPS := by
  rw [expandedSinhDivPS, expandedMomentQuarter]
  rw [← map_mul]
  congr 1
  rw [← map_mul]
  rw [mul_comm sinhDivPS momentPS, ← momentPS_functional]
  rw [PowerSeries.rescale_rescale]
  norm_num

private noncomputable def halfMomentCandidatePS : PowerSeries ℚ :=
  PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) * expandedMomentQuarter

private lemma halfMomentCandidatePS_functional :
    PowerSeries.rescale 2 halfMomentCandidatePS =
      expm1DivPSQ * halfMomentCandidatePS := by
  rw [halfMomentCandidatePS, map_mul]
  rw [PowerSeries.rescale_rescale, rescale_two_expandedMomentQuarter]
  norm_num
  rw [← mul_assoc, expm1DivPSQ_mul_exp_half]
  rw [mul_assoc, expandedSinhDivPS_mul_expandedMomentQuarter]

private lemma sum_range_even_div_two {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : ℕ → R) :
    (∑ x ∈ range (n + 1), if 2 ∣ x then f (x / 2) else 0) =
      ∑ k ∈ range (n / 2 + 1), f k := by
  rw [← Finset.sum_filter]
  have hfilter :
      (range (n + 1)).filter (fun x => 2 ∣ x) =
        (range (n / 2 + 1)).image (fun k => 2 * k) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, rfl⟩
      omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨by omega, ⟨k, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  · simp
  · intro a _ b _ hab
    change 2 * a = 2 * b at hab
    omega

private lemma coeff_exp_mul_expandedMomentQuarter (y : ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.rescale y (PowerSeries.exp ℚ) * expandedMomentQuarter) =
      (1 / ((2 : ℚ) ^ n * (n.factorial : ℚ))) *
        ∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) *
            (2 * y) ^ (n - 2 * k) * moment k := by
  rw [mul_comm, PowerSeries.coeff_mul]
  simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    expandedMomentQuarter, PowerSeries.coeff_expand,
    PowerSeries.coeff_rescale, momentPS, PowerSeries.coeff_mk,
    PowerSeries.coeff_exp]
  simp only [ite_mul, zero_mul]
  have hnormalize :
      (∑ x ∈ range n.succ,
        if 2 ∣ x then
          (1 / 4 : ℚ) ^ (x / 2) *
              (moment (x / 2) / ((2 * (x / 2)).factorial : ℚ)) *
            (y ^ (n - x) *
              (algebraMap ℚ ℚ) (1 / ((n - x).factorial : ℚ)))
        else 0) =
      ∑ x ∈ range (n + 1), if 2 ∣ x then
        ((1 / 4 : ℚ) ^ (x / 2) *
            (moment (x / 2) / ((2 * (x / 2)).factorial : ℚ))) *
          (y ^ (n - 2 * (x / 2)) *
            (1 / ((n - 2 * (x / 2)).factorial : ℚ)))
        else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hdiv : 2 ∣ x
    · obtain ⟨k, rfl⟩ := hdiv
      simp
    · simp [hdiv]
  rw [hnormalize]
  rw [sum_range_even_div_two n (fun k =>
    ((1 / 4 : ℚ) ^ k * (moment k / ((2 * k).factorial : ℚ))) *
      (y ^ (n - 2 * k) *
        (1 / ((n - 2 * k).factorial : ℚ))))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by
    have : k ≤ n / 2 := Nat.le_of_lt_succ (mem_range.1 hk)
    omega
  rw [Nat.cast_choose ℚ hk']
  norm_num [div_pow, pow_mul]
  field_simp
  have hn : n = 2 * k + (n - 2 * k) :=
    (Nat.add_sub_of_le hk').symm
  rw [hn, pow_add]
  norm_num [pow_mul]
  ring

private lemma coeff_halfMomentCandidatePS (n : ℕ) :
    PowerSeries.coeff n halfMomentCandidatePS =
      (∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) * moment k) /
        ((2 : ℚ) ^ n * (n.factorial : ℚ)) := by
  rw [halfMomentCandidatePS, coeff_exp_mul_expandedMomentQuarter]
  norm_num
  ring

/-- The centered even-moment series
`sum moment(k) X^(2k) / (4^k (2k)!)`.  Multiplication by `exp(X/2)`
recovers the factorially normalized half-moment series. -/
noncomputable def centeredMomentPowerSeries : PowerSeries ℚ :=
  expandedMomentQuarter

/-- The even coefficients of the centered series are the factorially
normalized moments, with the centering scale `4^n`. -/
@[simp] theorem coeff_centeredMomentPowerSeries_even (n : ℕ) :
    PowerSeries.coeff (2 * n) centeredMomentPowerSeries =
      moment n / ((4 : ℚ) ^ n * ((2 * n).factorial : ℚ)) := by
  simp [centeredMomentPowerSeries, expandedMomentQuarter, momentPS]
  ring

/-- The centered moment series has no odd-degree coefficients. -/
@[simp] theorem coeff_centeredMomentPowerSeries_odd (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) centeredMomentPowerSeries = 0 := by
  rw [centeredMomentPowerSeries, expandedMomentQuarter]
  apply PowerSeries.coeff_expand_of_not_dvd
  exact Nat.not_two_dvd_bit1 n

/-- Coefficients after translating the centered even-moment series by an
arbitrary rational amount. -/
theorem coeff_exp_mul_centeredMomentPowerSeries (y : ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.rescale y (PowerSeries.exp ℚ) *
        centeredMomentPowerSeries) =
      (1 / ((2 : ℚ) ^ n * (n.factorial : ℚ))) *
        ∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) *
            (2 * y) ^ (n - 2 * k) * moment k := by
  simpa only [centeredMomentPowerSeries] using
    coeff_exp_mul_expandedMomentQuarter y n

/-- Coefficients after translating the centered moment series by `1/2`.
This is the even-binomial transform appearing in Proposition 3. -/
theorem coeff_expHalf_mul_centeredMomentPowerSeries (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) *
          centeredMomentPowerSeries) =
      (∑ k ∈ range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℚ) * moment k) /
        ((2 : ℚ) ^ n * (n.factorial : ℚ)) := by
  simpa only [centeredMomentPowerSeries, halfMomentCandidatePS] using
    coeff_halfMomentCandidatePS n

private def halfMomentCandidate (n : ℕ) : ℚ :=
  (∑ k ∈ range (n / 2 + 1),
      (Nat.choose n (2 * k) : ℚ) * moment k) / (2 : ℚ) ^ n

private lemma coeff_halfMomentCandidatePS' (n : ℕ) :
    PowerSeries.coeff n halfMomentCandidatePS =
      halfMomentCandidate n / (n.factorial : ℚ) := by
  rw [coeff_halfMomentCandidatePS, halfMomentCandidate]
  field_simp

private lemma halfMomentCandidate_original_recurrence (n : ℕ) :
    (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n) * halfMomentCandidate n =
      ∑ k ∈ range (n + 1),
        (Nat.choose (n + 1) k : ℚ) * halfMomentCandidate k := by
  have hfun : PowerSeries.rescale 2 halfMomentCandidatePS =
      halfMomentCandidatePS * expm1DivPSQ := by
    simpa [mul_comm] using halfMomentCandidatePS_functional
  have h := congrArg (PowerSeries.coeff n) hfun
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, expm1DivPSQ,
    PowerSeries.coeff_mk] at h
  simp_rw [coeff_halfMomentCandidatePS'] at h
  have hleft :
      ((n + 1).factorial : ℚ) *
          ((2 : ℚ) ^ n *
            (halfMomentCandidate n / (n.factorial : ℚ))) =
        (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n) *
          halfMomentCandidate n := by
    rw [Nat.factorial_succ]
    field_simp
    push_cast
    ring
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      ((n + 1).factorial : ℚ) *
          (halfMomentCandidate k / (k.factorial : ℚ) *
            (1 / ((n - k + 1).factorial : ℚ))) =
        (Nat.choose (n + 1) k : ℚ) * halfMomentCandidate k := by
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
    have hk' : k ≤ n + 1 := hkn.trans (Nat.le_succ n)
    rw [Nat.cast_choose ℚ hk']
    have hsub : n + 1 - k = n - k + 1 := by omega
    rw [hsub]
    field_simp
  calc
    (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n) * halfMomentCandidate n =
        ((n + 1).factorial : ℚ) *
          ((2 : ℚ) ^ n *
            (halfMomentCandidate n / (n.factorial : ℚ))) := hleft.symm
    _ = ((n + 1).factorial : ℚ) *
        (∑ x ∈ range n.succ,
          halfMomentCandidate x / (x.factorial : ℚ) *
            (1 / ((n - x + 1).factorial : ℚ))) := by rw [h]
    _ = ∑ k ∈ range (n + 1),
        (Nat.choose (n + 1) k : ℚ) * halfMomentCandidate k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm k hk

@[simp] private lemma halfMomentCandidate_zero : halfMomentCandidate 0 = 1 := by
  norm_num [halfMomentCandidate, moment]

private lemma halfMomentCandidate_succ (n : ℕ) :
    halfMomentCandidate (n + 1) =
      (∑ k : Fin (n + 1),
          (Nat.choose (n + 2) k.val : ℚ) * halfMomentCandidate k.val) /
        (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1)) := by
  have h := halfMomentCandidate_original_recurrence (n + 1)
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (Nat.choose (n + 2) k : ℚ) * halfMomentCandidate k) (n + 1)]
  rw [sum_range_succ] at h
  have hchoose : (n + 2).choose (n + 1) = n + 2 := by
    exact Nat.choose_succ_self_right (n + 1)
  rw [hchoose] at h
  have hpow : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hfactor : ((n + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast at h ⊢
  linear_combination h

/-- Proposition 3: the half moments are the even-binomial transform of the moments. -/
theorem halfMoment_eq_evenMomentSum (n : ℕ) :
    halfMoment n =
      (∑ k ∈ range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℚ) * moment k) / (2 : ℚ) ^ n := by
  change halfMoment n = halfMomentCandidate n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [halfMoment_succ, halfMomentCandidate_succ]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k.val k.isLt]

/-- Multiplying the centered moment series by `exp(X/2)` produces the
factorially normalized half-moment series coefficient by coefficient. -/
theorem coeff_expHalf_mul_centeredMomentPowerSeries_eq_halfMoment (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) *
          centeredMomentPowerSeries) =
      halfMoment n / (n.factorial : ℚ) := by
  rw [coeff_expHalf_mul_centeredMomentPowerSeries,
    halfMoment_eq_evenMomentSum]
  field_simp

/-- Odd half moments reduce to a single even moment. -/
theorem halfMoment_odd_eq_moment (n : ℕ) :
    halfMoment (2 * n + 1) = ((2 * n + 1 : ℕ) : ℚ) / 2 * moment n := by
  rw [halfMoment_eq_evenMomentSum]
  rw [show (2 * n + 1) / 2 = n by omega]
  have h := moment_original_recurrence n
  rw [← h]
  rw [pow_succ]
  field_simp

/-- Equation (32) at numerator one agrees with the half-moment formula (22). -/
theorem fabiusAtInverseTwoPow_eq_halfMoment (n : ℕ) :
    fabiusAtInverseTwoPow n = halfMomentFabiusValue n := by
  rw [fabiusAtInverseTwoPow, fabiusDyadic, halfMomentFabiusValue,
    halfMoment_eq_evenMomentSum]
  norm_num [thueMorseSign, binaryWeight]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (Nat.choose n (2 * k) : ℚ) * moment k) (n / 2 + 1)]
  have hchoose : (n + 1).choose 2 = n + n.choose 2 := by
    simp [Nat.choose_succ_succ, Nat.choose_one_right]
  rw [hchoose, pow_add]
  field_simp

end Fabius
