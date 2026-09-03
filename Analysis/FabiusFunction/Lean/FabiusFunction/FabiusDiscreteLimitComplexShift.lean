import FabiusFunction.Arithmetic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Complex translations of the finite Thue--Morse spline branches

This module isolates the complex-analytic ingredient in the discrete-limit
formula for the signed global Fabius function.  A branch is a normalized
finite Thue--Morse power sum with a fixed cutoff.  Translating its argument
has an exact finite Taylor expansion in the lower-degree branches.  Under a
unit bound for those lower branches, this gives a uniform exponential
translation estimate with no constant term in the translation increment.  The
estimate holds in every degree, including degree zero, where the branch is
independent of its complex argument.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- The normalized degree-`p` Thue--Morse polynomial with a fixed prefix
length `M`.  Keeping `M` separate from the evaluation point is important:
the complex translation stays on one real spline branch. -/
def normalizedThueMorseSplineBranch
    (p M : ℕ) (z : ℂ) : ℂ :=
  (∑ r ∈ Finset.range M,
      (thueMorseSign r : ℂ) * (z - (r : ℂ)) ^ p) /
    ((2 : ℂ) ^ p.choose 2 * (p.factorial : ℂ))

/-- A normalized Thue--Morse spline branch with empty prefix is identically zero. -/
@[simp] theorem normalizedThueMorseSplineBranch_zero_prefix
    (p : ℕ) (z : ℂ) :
    normalizedThueMorseSplineBranch p 0 z = 0 := by
  simp [normalizedThueMorseSplineBranch]

private theorem choose_div_factorial_complex
    {p d : ℕ} (hd : d ≤ p) :
    (p.choose d : ℂ) / (p.factorial : ℂ) =
      1 / ((d.factorial : ℂ) * ((p - d).factorial : ℂ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial hd
  have hcast :
      (p.choose d : ℂ) * (d.factorial : ℂ) *
          ((p - d).factorial : ℂ) = (p.factorial : ℂ) := by
    exact_mod_cast hnat
  have hp : (p.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  have hd' : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hpd : ((p - d).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (p - d))
  field_simp [hp, hd', hpd]
  exact hcast

private theorem thueMorsePrefix_add_pow
    (p M : ℕ) (z δ : ℂ) :
    (∑ r ∈ Finset.range M,
        (thueMorseSign r : ℂ) * (z + δ - (r : ℂ)) ^ p) =
      ∑ d ∈ Finset.range (p + 1),
        (p.choose d : ℂ) * δ ^ (p - d) *
          ∑ r ∈ Finset.range M,
            (thueMorseSign r : ℂ) * (z - (r : ℂ)) ^ d := by
  simp_rw [show ∀ r : ℕ,
      z + δ - (r : ℂ) = (z - (r : ℂ)) + δ by intro r; ring]
  simp_rw [show ∀ (a b : ℂ),
      (a + b) ^ p = ∑ m ∈ Finset.range (p + 1),
        a ^ m * b ^ (p - m) * (p.choose m : ℂ) by
          intro a b
          exact (Commute.all a b).add_pow p,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Exact finite Taylor expansion of a fixed spline branch.  The index `d`
is the degree of the lower branch; equivalently, `p-d` is the Taylor order. -/
theorem normalizedThueMorseSplineBranch_add
    (p M : ℕ) (z δ : ℂ) :
    normalizedThueMorseSplineBranch p M (z + δ) =
      ∑ d ∈ Finset.range (p + 1),
        ((2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))) *
          δ ^ (p - d) * normalizedThueMorseSplineBranch d M z := by
  rw [normalizedThueMorseSplineBranch, thueMorsePrefix_add_pow]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp : d ≤ p := by simpa using Finset.mem_range.mp hd
  rw [normalizedThueMorseSplineBranch]
  field_simp [Nat.cast_ne_zero]
  calc
    ((p.choose d : ℂ) * δ ^ (p - d) *
          ∑ x ∈ Finset.range M,
            (thueMorseSign x : ℂ) * (z - (x : ℂ)) ^ d) /
        (p.factorial : ℂ) =
        ((p.choose d : ℂ) / (p.factorial : ℂ)) *
          (δ ^ (p - d) *
            ∑ x ∈ Finset.range M,
              (thueMorseSign x : ℂ) * (z - (x : ℂ)) ^ d) := by ring
    _ =
        (1 / ((d.factorial : ℂ) * ((p - d).factorial : ℂ))) *
          (δ ^ (p - d) *
            ∑ x ∈ Finset.range M,
              (thueMorseSign x : ℂ) * (z - (x : ℂ)) ^ d) := by
          rw [choose_div_factorial_complex hdp]
    _ =
        (δ ^ (p - d) *
          ∑ x ∈ Finset.range M,
            (thueMorseSign x : ℂ) * (z - (x : ℂ)) ^ d) /
          (((p - d).factorial : ℂ) * (d.factorial : ℂ)) := by ring

/-- The positive Taylor orders are exactly the change under translation. -/
theorem normalizedThueMorseSplineBranch_add_sub
    (p M : ℕ) (z δ : ℂ) :
    normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z =
      ∑ d ∈ Finset.range p,
        ((2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))) *
          δ ^ (p - d) * normalizedThueMorseSplineBranch d M z := by
  rw [normalizedThueMorseSplineBranch_add, Finset.sum_range_succ]
  have hpow : (2 : ℂ) ^ p.choose 2 ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [hpow]

/-- A norm bound for a translated branch when all lower branches in its
Taylor expansion are bounded by a common constant `B`.  The bound is useful
independently of the Fabius application, where `B = 1`. -/
theorem norm_normalizedThueMorseSplineBranch_add_sub_le_mul_sum
    (p M : ℕ) (z δ : ℂ)
    (B : ℝ)
    (hbound : ∀ d ∈ Finset.range p,
      ‖normalizedThueMorseSplineBranch d M z‖ ≤ B) :
    ‖normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z‖ ≤
      B * ∑ d ∈ Finset.range p,
          ‖(2 : ℂ) ^ d.choose 2 /
              ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ *
            ‖δ‖ ^ (p - d) := by
  rw [normalizedThueMorseSplineBranch_add_sub]
  calc
    ‖∑ d ∈ Finset.range p,
        ((2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))) *
          δ ^ (p - d) * normalizedThueMorseSplineBranch d M z‖ ≤
        ∑ d ∈ Finset.range p,
          ‖((2 : ℂ) ^ d.choose 2 /
              ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))) *
            δ ^ (p - d) * normalizedThueMorseSplineBranch d M z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.range p, B *
        (‖(2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ *
          ‖δ‖ ^ (p - d)) := by
      apply Finset.sum_le_sum
      intro d hd
      simp only [norm_mul, norm_pow]
      let A : ℝ :=
        ‖(2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ *
          ‖δ‖ ^ (p - d)
      change A * ‖normalizedThueMorseSplineBranch d M z‖ ≤ B * A
      calc
        A * ‖normalizedThueMorseSplineBranch d M z‖ ≤ A * B :=
          mul_le_mul_of_nonneg_left (hbound d hd) (by positivity)
        _ = B * A := mul_comm A B
    _ = B * ∑ d ∈ Finset.range p,
        ‖(2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ *
          ‖δ‖ ^ (p - d) := by
      rw [Finset.mul_sum]

/-- A norm bound for the translated branch, assuming that all lower
branches occurring in its Taylor expansion have norm at most one. -/
theorem norm_normalizedThueMorseSplineBranch_add_sub_le
    (p M : ℕ) (z δ : ℂ)
    (hbound : ∀ d ∈ Finset.range p,
      ‖normalizedThueMorseSplineBranch d M z‖ ≤ 1) :
    ‖normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z‖ ≤
      ∑ d ∈ Finset.range p,
        ‖(2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ *
          ‖δ‖ ^ (p - d) := by
  simpa using
    norm_normalizedThueMorseSplineBranch_add_sub_le_mul_sum
      p M z δ 1 hbound

private theorem norm_complex_two_choose_factor
    (p d : ℕ) :
    ‖(2 : ℂ) ^ d.choose 2 /
        ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ =
      (2 : ℝ) ^ d.choose 2 /
        ((2 : ℝ) ^ p.choose 2 * ((p - d).factorial : ℝ)) := by
  simp [norm_pow]

private theorem norm_complex_two_choose_factor_le
    {p d : ℕ} (hp : 1 ≤ p) (hd : d < p) :
    ‖(2 : ℂ) ^ d.choose 2 /
        ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) / ((p - d).factorial : ℝ) := by
  cases p with
  | zero => simp at hp
  | succ a =>
    rw [norm_complex_two_choose_factor]
    have hda : d ≤ a := Nat.le_of_lt_succ hd
    have hchoose : d.choose 2 ≤ a.choose 2 :=
      Nat.choose_le_choose 2 hda
    have hpow :
        (2 : ℝ) ^ d.choose 2 ≤ (2 : ℝ) ^ a.choose 2 :=
      pow_le_pow_right₀ (by norm_num) hchoose
    rw [choose_succ_two]
    have hscale :
        (1 / 2 : ℝ) ^ (a + 1 - 1) *
            (2 : ℝ) ^ (a.choose 2 + a) =
          (2 : ℝ) ^ a.choose 2 := by
      simp only [Nat.add_sub_cancel, pow_add]
      calc
        (1 / 2 : ℝ) ^ a *
            ((2 : ℝ) ^ a.choose 2 * (2 : ℝ) ^ a) =
            (2 : ℝ) ^ a.choose 2 *
              ((1 / 2 : ℝ) ^ a * (2 : ℝ) ^ a) := by ring
        _ = (2 : ℝ) ^ a.choose 2 := by
          rw [← mul_pow]
          norm_num
    have hratio :
        (2 : ℝ) ^ d.choose 2 / (2 : ℝ) ^ (a.choose 2 + a) ≤
          (1 / 2 : ℝ) ^ (a + 1 - 1) := by
      rw [div_le_iff₀ (by positivity)]
      rw [hscale]
      exact hpow
    calc
      (2 : ℝ) ^ d.choose 2 /
            ((2 : ℝ) ^ (a.choose 2 + a) *
              ((a + 1 - d).factorial : ℝ)) =
          ((2 : ℝ) ^ d.choose 2 /
            (2 : ℝ) ^ (a.choose 2 + a)) /
              ((a + 1 - d).factorial : ℝ) := by ring
      _ ≤ (1 / 2 : ℝ) ^ (a + 1 - 1) /
            ((a + 1 - d).factorial : ℝ) := by
        exact div_le_div_of_nonneg_right hratio (by positivity)

private theorem reflected_factorial_sum_le_exp_sub_one
    (R : ℝ) (hR : 0 ≤ R) (p : ℕ) :
    (∑ d ∈ Finset.range p,
        R ^ (p - d) / ((p - d).factorial : ℝ)) ≤ Real.exp R - 1 := by
  let f : ℕ → ℝ := fun j => R ^ j / (j.factorial : ℝ)
  calc
    (∑ d ∈ Finset.range p,
        R ^ (p - d) / ((p - d).factorial : ℝ)) =
        ∑ j ∈ Finset.Ico 1 (p + 1), f j := by
      simpa [f, Nat.Ico_zero_eq_range] using
        (Finset.sum_Ico_reflect f 0 (m := p) (n := p) (Nat.le_succ p))
    _ ≤ Real.exp R - 1 := by
      rw [Finset.sum_Ico_eq_sub f
        (Nat.succ_le_succ (Nat.zero_le p))]
      simpa [f] using
        sub_le_sub_right (Real.sum_le_exp_of_nonneg hR (p + 1)) 1

/-- A complex branch translation is controlled by the exponential increment.
The reflected Taylor order starts at one, so the majorant has no constant term
in `δ`. -/
theorem norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_sub_one
    (p M : ℕ) (z δ : ℂ) (hp : 1 ≤ p)
    (hbound : ∀ d ∈ Finset.range p,
      ‖normalizedThueMorseSplineBranch d M z‖ ≤ 1) :
    ‖normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) * (Real.exp ‖δ‖ - 1) := by
  calc
    ‖normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z‖ ≤
      ∑ d ∈ Finset.range p,
        ‖(2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))‖ *
          ‖δ‖ ^ (p - d) :=
      norm_normalizedThueMorseSplineBranch_add_sub_le p M z δ hbound
    _ ≤ ∑ d ∈ Finset.range p,
        ((1 / 2 : ℝ) ^ (p - 1) / ((p - d).factorial : ℝ)) *
          ‖δ‖ ^ (p - d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right
        (norm_complex_two_choose_factor_le hp (Finset.mem_range.mp hd))
        (by positivity)
    _ = (1 / 2 : ℝ) ^ (p - 1) *
        (∑ d ∈ Finset.range p,
          ‖δ‖ ^ (p - d) / ((p - d).factorial : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (1 / 2 : ℝ) ^ (p - 1) * (Real.exp ‖δ‖ - 1) :=
      mul_le_mul_of_nonneg_left
        (reflected_factorial_sum_le_exp_sub_one ‖δ‖ (norm_nonneg δ) p)
        (by positivity)

/-- Uniform quantitative control of a complex translation of one branch.
The factor `(1/2)^(p-1)` is independent of the real branch and tends to zero. -/
theorem norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp
    (p M : ℕ) (z δ : ℂ) (hp : 1 ≤ p)
    (hbound : ∀ d ∈ Finset.range p,
      ‖normalizedThueMorseSplineBranch d M z‖ ≤ 1) :
    ‖normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) * Real.exp ‖δ‖ := by
  exact
    (norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_sub_one
      p M z δ hp hbound).trans
      (mul_le_mul_of_nonneg_left
        (sub_le_self (Real.exp ‖δ‖) zero_le_one) (by positivity))

/-- The exponential-increment translation bound holds in every degree.  At
`p = 0` the branch difference and its finite Taylor majorant both vanish. -/
theorem
    norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_sub_one_all
    (p M : ℕ) (z δ : ℂ)
    (hbound : ∀ d ∈ Finset.range p,
      ‖normalizedThueMorseSplineBranch d M z‖ ≤ 1) :
    ‖normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) * (Real.exp ‖δ‖ - 1) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact le_trans
      (norm_normalizedThueMorseSplineBranch_add_sub_le 0 M z δ hbound)
      (by
        simpa only [Finset.range_zero, Finset.sum_empty, Nat.zero_sub,
          pow_zero, one_mul] using
          sub_nonneg.mpr (Real.one_le_exp (norm_nonneg δ)))
  · exact
      norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_sub_one
        p M z δ hp hbound

/-- Uniform quantitative control of a complex branch translation in every
degree.  At `p = 0` the branch is independent of its complex argument, the
lower-degree hypothesis is vacuous, and the naturally truncated exponent
`p - 1` is zero. -/
theorem norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_all
    (p M : ℕ) (z δ : ℂ)
    (hbound : ∀ d ∈ Finset.range p,
      ‖normalizedThueMorseSplineBranch d M z‖ ≤ 1) :
    ‖normalizedThueMorseSplineBranch p M (z + δ) -
        normalizedThueMorseSplineBranch p M z‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) * Real.exp ‖δ‖ := by
  exact
    (norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_sub_one_all
      p M z δ hbound).trans
      (mul_le_mul_of_nonneg_left
        (sub_le_self (Real.exp ‖δ‖) zero_le_one) (by positivity))

end

end Fabius
