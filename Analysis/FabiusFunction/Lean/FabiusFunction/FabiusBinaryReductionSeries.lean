import FabiusFunction.TaylorReduction
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.EMetricSpace.Basic

/-!
# A global binary-reduction series for the Fabius function

This module iterates the finite Taylor reduction along the binary expansion
of a nonnegative real number.  The outer index starts at `m = 0`.  This is
essential: at scale zero, `Floor[2^(m-1)x]` is `Floor[x/2]`, and the resulting
term distinguishes the even and odd unit blocks of the signed global Fabius
extension.

The exact finite identity has a signed residual term.  On nonnegative inputs,
binary tails tend to zero; on nonpositive inputs, the residual vanishes
termwise.  Its input-independent geometric bound holds at every natural scale,
including zero, and proves uniform convergence of the finite telescopes on the
real line.  Every positive-index summand has a
uniform geometric majorant on all of `ℝ`, so the summand norms are summable
there.  Since both the summand and the signed extension vanish identically on
the nonpositive half-line, the resulting `HasSum` and `tsum` identities are
stated on all of `ℝ`; the established nonnegative signatures remain as
compatibility wrappers.  The shifted series starting at `m = 1` consequently
holds on the full domain `x < 1` where its omitted scale-zero term vanishes.

The elementary binary API is stated uniformly at every scale, including
`m = 0`: the previous prefix is the quotient of the current prefix by two,
the remainder modulo two is the next binary digit, and clearing the power-of-
two denominator recovers the defining prefix exactly.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set Filter Topology

namespace Fabius

noncomputable section

/-- `Floor[2^m x]` on the nonnegative half-line. -/
def binaryPrefix (x : ℝ) (m : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ m * x⌋₊

/-- The tail left after truncating the binary expansion after `m` places. -/
def binaryTail (x : ℝ) (m : ℕ) : ℝ :=
  x - (binaryPrefix x m : ℝ) / (2 : ℝ) ^ m

/-- Every natural binary prefix is zero at a nonpositive input. -/
@[simp] theorem binaryPrefix_eq_zero_of_nonpos
    (m : ℕ) {x : ℝ} (hx : x ≤ 0) :
    binaryPrefix x m = 0 := by
  rw [binaryPrefix, Nat.floor_eq_zero]
  have hnonpos : (2 : ℝ) ^ m * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
  linarith

/-- On the nonpositive half-line truncation removes no fractional prefix. -/
@[simp] theorem binaryTail_eq_self_of_nonpos
    (m : ℕ) {x : ℝ} (hx : x ≤ 0) :
    binaryTail x m = x := by
  rw [binaryTail, binaryPrefix_eq_zero_of_nonpos m hx]
  norm_num

/-- Clearing the scale denominator in a binary tail recovers the prefix
subtraction exactly. -/
theorem two_pow_mul_binaryTail (x : ℝ) (m : ℕ) :
    (2 : ℝ) ^ m * binaryTail x m =
      (2 : ℝ) ^ m * x - binaryPrefix x m := by
  rw [binaryTail, mul_sub]
  have hpow : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp

/-- The twice-scaled form used by the global q-binomial summand. -/
theorem two_pow_succ_mul_binaryTail (x : ℝ) (m : ℕ) :
    (2 : ℝ) ^ (m + 1) * binaryTail x m =
      (2 : ℝ) ^ (m + 1) * x - 2 * binaryPrefix x m := by
  calc
    (2 : ℝ) ^ (m + 1) * binaryTail x m =
        2 * ((2 : ℝ) ^ m * binaryTail x m) := by
      rw [pow_succ]
      ring
    _ = 2 * ((2 : ℝ) ^ m * x - binaryPrefix x m) := by
      rw [two_pow_mul_binaryTail]
    _ = (2 : ℝ) ^ (m + 1) * x - 2 * binaryPrefix x m := by
      rw [pow_succ]
      ring

/-- `Floor[2^(m-1)x]`, including the genuine half-scale value at `m = 0`. -/
def binaryPreviousPrefix (x : ℝ) : ℕ → ℕ
  | 0 => ⌊x / 2⌋₊
  | m + 1 => binaryPrefix x m

/-- Literal identification with `Floor[2^(m-1)x]`, including `m = 0`. -/
theorem binaryPreviousPrefix_eq_floor_zpow (x : ℝ) (m : ℕ) :
    binaryPreviousPrefix x m =
      ⌊(2 : ℝ) ^ ((m : ℤ) - 1) * x⌋₊ := by
  cases m with
  | zero =>
      simp [binaryPreviousPrefix]
      congr 2
      ring
  | succ m =>
      simp [binaryPreviousPrefix, binaryPrefix]

/-- At every scale, the previous binary prefix is the natural-number quotient
of the current prefix by two.  The statement includes the half-scale
definition at `m = 0`. -/
theorem binaryPreviousPrefix_eq_binaryPrefix_div_two (x : ℝ) (m : ℕ) :
    binaryPreviousPrefix x m = binaryPrefix x m / 2 := by
  cases m with
  | zero =>
      rw [binaryPreviousPrefix, binaryPrefix]
      norm_num
      exact Nat.floor_div_natCast x 2
  | succ m =>
      rw [binaryPreviousPrefix, binaryPrefix, binaryPrefix]
      have harg :
          (2 : ℝ) ^ m * x = ((2 : ℝ) ^ (m + 1) * x) / 2 := by
        rw [pow_succ]
        ring
      rw [harg]
      exact Nat.floor_div_natCast ((2 : ℝ) ^ (m + 1) * x) 2

/-- The half-scale predecessor is also zero at every nonpositive input. -/
@[simp] theorem binaryPreviousPrefix_eq_zero_of_nonpos
    (m : ℕ) {x : ℝ} (hx : x ≤ 0) :
    binaryPreviousPrefix x m = 0 := by
  rw [binaryPreviousPrefix_eq_binaryPrefix_div_two,
    binaryPrefix_eq_zero_of_nonpos m hx]

/-- Exact quotient-remainder decomposition of a binary prefix.  The final
term, `binaryPrefix x m % 2`, is the binary digit exposed at scale `m`. -/
theorem binaryPrefix_eq_two_mul_previous_add_mod_two (x : ℝ) (m : ℕ) :
    binaryPrefix x m =
      2 * binaryPreviousPrefix x m + binaryPrefix x m % 2 := by
  rw [binaryPreviousPrefix_eq_binaryPrefix_div_two]
  omega

/-- A binary prefix is either twice its previous prefix or its successor.
Unlike the internal induction step, this formulation is valid uniformly at
scale zero. -/
theorem binaryPrefix_eq_two_mul_previous_or_succ (x : ℝ) (m : ℕ) :
    binaryPrefix x m = 2 * binaryPreviousPrefix x m ∨
      binaryPrefix x m = 2 * binaryPreviousPrefix x m + 1 := by
  have hmod : binaryPrefix x m % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdecomp := binaryPrefix_eq_two_mul_previous_add_mod_two x m
  interval_cases h : binaryPrefix x m % 2
  · left
    omega
  · right
    omega

/-- The signed binary-digit coefficient in the outer series. -/
def globalBinaryReductionCoefficient (x : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) *
    (2 * (binaryPreviousPrefix x m : ℝ) - (binaryPrefix x m : ℝ))

/-- Exact all-scale coefficient formula in terms of the exposed binary digit.
The statement includes `m = 0`, where `binaryPreviousPrefix` is the genuine
half-scale floor. -/
theorem globalBinaryReductionCoefficient_eq_neg_mod_two
    (x : ℝ) (m : ℕ) :
    globalBinaryReductionCoefficient x m =
      (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) *
        (-((binaryPrefix x m % 2 : ℕ) : ℝ)) := by
  rw [globalBinaryReductionCoefficient]
  have hprefix :
      (binaryPrefix x m : ℝ) =
        2 * (binaryPreviousPrefix x m : ℝ) +
          ((binaryPrefix x m % 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ))
        (binaryPrefix_eq_two_mul_previous_add_mod_two x m)
  rw [hprefix]
  ring

/-- An even exposed binary digit makes the all-scale coefficient vanish. -/
theorem globalBinaryReductionCoefficient_eq_zero_of_mod_two_eq_zero
    (x : ℝ) (m : ℕ) (hbit : binaryPrefix x m % 2 = 0) :
    globalBinaryReductionCoefficient x m = 0 := by
  rw [globalBinaryReductionCoefficient_eq_neg_mod_two, hbit]
  norm_num

/-- An odd exposed binary digit leaves the sign of the previous prefix.  This
is the all-scale version of the coefficient branch used in the telescope. -/
theorem globalBinaryReductionCoefficient_eq_previous_sign_of_mod_two_eq_one
    (x : ℝ) (m : ℕ) (hbit : binaryPrefix x m % 2 = 1) :
    globalBinaryReductionCoefficient x m =
      (-1 : ℝ) ^ binaryWeight (binaryPreviousPrefix x m) := by
  have hprefix :
      binaryPrefix x m = 2 * binaryPreviousPrefix x m + 1 := by
    calc
      binaryPrefix x m =
          2 * binaryPreviousPrefix x m + binaryPrefix x m % 2 :=
        binaryPrefix_eq_two_mul_previous_add_mod_two x m
      _ = 2 * binaryPreviousPrefix x m + 1 := by rw [hbit]
  rw [globalBinaryReductionCoefficient_eq_neg_mod_two, hbit, hprefix,
    binaryWeight_two_mul_add_one, pow_succ]
  ring

/-- The analytic outer summand before substituting explicit formulas for the
inverse-power constants in `fabiusReductionSum`. -/
def globalBinaryReductionSummand (x : ℝ) (m : ℕ) : ℝ :=
  globalBinaryReductionCoefficient x m *
    fabiusReductionSum m (binaryTail x m)

/-- Every binary-reduction summand vanishes at a nonpositive input.  Lean's
natural floor makes every binary prefix zero there, matching the convention
that the signed extension itself vanishes on the negative half-line. -/
@[simp] theorem globalBinaryReductionSummand_eq_zero_of_nonpos
    (m : ℕ) {x : ℝ} (hx : x ≤ 0) :
    globalBinaryReductionSummand x m = 0 := by
  rw [globalBinaryReductionSummand,
    globalBinaryReductionCoefficient_eq_neg_mod_two,
    binaryPrefix_eq_zero_of_nonpos m hx]
  norm_num

/-- The signed residual term after the first `N` fractional binary digits. -/
def binaryReductionRemainder (F : BoundedFabius) (x : ℝ) (N : ℕ) : ℝ :=
  (-1 : ℝ) ^ binaryWeight (binaryPrefix x N) *
    extendedFabius F (binaryTail x N)

/-- The signed residual vanishes at every nonpositive input and every scale. -/
@[simp] theorem binaryReductionRemainder_eq_zero_of_nonpos
    (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) {x : ℝ} (hx : x ≤ 0) :
    binaryReductionRemainder F x N = 0 := by
  rw [binaryReductionRemainder, binaryPrefix_eq_zero_of_nonpos N hx,
    binaryTail_eq_self_of_nonpos N hx,
    extendedFabius_eq_zero_of_nonpos F hF hx]
  norm_num

/-- For a nonnegative argument the binary tail at every scale is
nonnegative. -/
theorem binaryTail_nonneg (x : ℝ) (m : ℕ) (hx : 0 ≤ x) :
    0 ≤ binaryTail x m := by
  rw [binaryTail]
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  rw [sub_nonneg, div_le_iff₀ hp]
  have h := Nat.floor_le (mul_nonneg (show (0 : ℝ) ≤ 2 ^ m by positivity) hx)
  dsimp only [binaryPrefix] at h ⊢
  nlinarith

/-- The binary tail at scale `m` is strictly less than `2 ^ (-m)`.
No sign hypothesis on `x` is required. -/
theorem binaryTail_lt (x : ℝ) (m : ℕ) :
    binaryTail x m < ((2 : ℝ) ^ m)⁻¹ := by
  rw [binaryTail]
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hfloor := Nat.lt_floor_add_one ((2 : ℝ) ^ m * x)
  rw [show ((2 : ℝ) ^ m)⁻¹ = 1 / (2 : ℝ) ^ m by simp]
  apply (sub_lt_iff_lt_add).2
  have hdiv : x < ((binaryPrefix x m : ℝ) + 1) / (2 : ℝ) ^ m := by
    apply (lt_div_iff₀ hp).2
    dsimp only [binaryPrefix]
    simpa only [mul_comm] using hfloor
  simpa only [add_div, add_comm] using hdiv

private lemma binaryPrefix_pred_eq_div_two
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    binaryPrefix x (m - 1) = binaryPrefix x m / 2 := by
  rw [← binaryPreviousPrefix_eq_binaryPrefix_div_two]
  cases m with
  | zero => omega
  | succ m => rfl

private lemma binaryPrefix_eq_double_or_succ
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    binaryPrefix x m = 2 * binaryPrefix x (m - 1) ∨
      binaryPrefix x m = 2 * binaryPrefix x (m - 1) + 1 := by
  have hprev : binaryPreviousPrefix x m = binaryPrefix x (m - 1) := by
    rw [binaryPreviousPrefix_eq_binaryPrefix_div_two,
      ← binaryPrefix_pred_eq_div_two x m hm]
  simpa only [hprev] using binaryPrefix_eq_two_mul_previous_or_succ x m

private lemma binaryTail_step_zero
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hzero : binaryPrefix x m = 2 * binaryPrefix x (m - 1)) :
    binaryTail x (m - 1) = binaryTail x m := by
  rw [binaryTail, binaryTail, hzero]
  have hmEq : m = (m - 1) + 1 := by omega
  rw [hmEq, pow_succ]
  push_cast
  field_simp

private lemma binaryTail_step_one
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hone : binaryPrefix x m = 2 * binaryPrefix x (m - 1) + 1) :
    binaryTail x (m - 1) =
      (2 : ℝ) ^ (-(m : ℤ)) + binaryTail x m := by
  rw [binaryTail, binaryTail, hone]
  have hmEq : m = (m - 1) + 1 := by omega
  rw [hmEq, pow_succ]
  rw [zpow_neg, zpow_natCast]
  push_cast
  field_simp
  ring

private lemma globalBinaryReductionCoefficient_of_zero
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hzero : binaryPrefix x m = 2 * binaryPrefix x (m - 1)) :
    globalBinaryReductionCoefficient x m = 0 := by
  cases m with
  | zero => omega
  | succ m =>
      apply globalBinaryReductionCoefficient_eq_zero_of_mod_two_eq_zero
      rw [hzero]
      omega

private lemma globalBinaryReductionCoefficient_of_one
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hone : binaryPrefix x m = 2 * binaryPrefix x (m - 1) + 1) :
    globalBinaryReductionCoefficient x m =
      (-1 : ℝ) ^ binaryWeight (binaryPrefix x (m - 1)) := by
  have hbit : binaryPrefix x m % 2 = 1 := by
    rw [hone]
    omega
  rw [globalBinaryReductionCoefficient_eq_previous_sign_of_mod_two_eq_one
    x m hbit]
  cases m with
  | zero => omega
  | succ m => rfl

/-- The scale-zero step.  It distinguishes even and odd unit blocks and is
the term missing from a series whose outer index incorrectly starts at one. -/
theorem extendedFabius_eq_globalBinaryReduction_zero_add_remainder
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) :
    extendedFabius F x =
      globalBinaryReductionSummand x 0 + binaryReductionRemainder F x 0 := by
  let a := binaryPrefix x 0
  let b := binaryPreviousPrefix x 0
  let y := binaryTail x 0
  let z := x - 2 * (b : ℝ)
  have hy0 : 0 ≤ y := binaryTail_nonneg x 0 hx0
  have hy1 : y < 1 := by
    simpa only [inv_pow, pow_zero, inv_one] using binaryTail_lt x 0
  have hxform : x = (a : ℝ) + y := by
    simp only [a, y, binaryTail, pow_zero, div_one]
    ring
  have hab := binaryPrefix_eq_two_mul_previous_or_succ x 0
  change a = 2 * b ∨ a = 2 * b + 1 at hab
  rcases hab with heven | hodd
  · have hzform : z = y := by
      dsimp only [z]
      rw [hxform, heven]
      push_cast
      ring
    have hblockX := extendedFabius_eq_single_translate F hF b
      (show 2 * (b : ℝ) ≤ x by rw [hxform, heven]; push_cast; linarith)
      (show x ≤ 2 * (b : ℝ) + 2 by rw [hxform, heven]; push_cast; linarith)
    have hblockZ' : extendedFabius F z = rvachevUp F (z - 1) :=
      extendedFabius_eq_rvachevUp_sub_one F hF (by rw [hzform]; linarith)
    have hglobal : extendedFabius F x =
        (-1 : ℝ) ^ binaryWeight b * extendedFabius F y := by
      rw [hblockX, ← hblockZ', hzform]
    rw [hglobal]
    simp only [globalBinaryReductionSummand,
      globalBinaryReductionCoefficient, binaryReductionRemainder]
    change (-1 : ℝ) ^ binaryWeight b * extendedFabius F y =
      (-1 : ℝ) ^ binaryWeight a *
          (2 * (b : ℝ) - (a : ℝ)) * fabiusReductionSum 0 y +
        (-1 : ℝ) ^ binaryWeight a * extendedFabius F y
    rw [heven, binaryWeight_two_mul]
    push_cast
    ring
  · have hzform : z = 1 + y := by
      dsimp only [z]
      rw [hxform, hodd]
      push_cast
      ring
    have hblockX := extendedFabius_eq_single_translate F hF b
      (show 2 * (b : ℝ) ≤ x by rw [hxform, hodd]; push_cast; linarith)
      (show x ≤ 2 * (b : ℝ) + 2 by rw [hxform, hodd]; push_cast; linarith)
    have hblockZ' : extendedFabius F z = rvachevUp F (z - 1) :=
      extendedFabius_eq_rvachevUp_sub_one F hF (by rw [hzform]; linarith)
    have hglobal : extendedFabius F x =
        (-1 : ℝ) ^ binaryWeight b * extendedFabius F z := by
      rw [hblockX, ← hblockZ']
    have hzpos : 0 < z := by rw [hzform]; linarith
    have hzlo : (2 : ℝ) ^ (-(0 : ℤ)) ≤ z := by
      norm_num [hzform]
      exact hy0
    have hzhi : z < (2 : ℝ) ^ (-(0 : ℤ) + 1) := by
      norm_num [hzform]
      linarith
    have hreduce := extendedFabius_reduction F hF z 0 hzpos hzlo hzhi
    have hreduce' : extendedFabius F z =
        -extendedFabius F y + fabiusReductionSum 0 y := by
      simpa [hzform] using hreduce
    rw [hglobal, hreduce']
    simp only [globalBinaryReductionSummand,
      globalBinaryReductionCoefficient, binaryReductionRemainder]
    change (-1 : ℝ) ^ binaryWeight b *
        (-extendedFabius F y + fabiusReductionSum 0 y) =
      (-1 : ℝ) ^ binaryWeight a *
          (2 * (b : ℝ) - (a : ℝ)) * fabiusReductionSum 0 y +
        (-1 : ℝ) ^ binaryWeight a * extendedFabius F y
    rw [hodd, binaryWeight_two_mul_add_one, pow_succ]
    push_cast
    ring

/-- The exact global finite telescope, including scale zero. -/
theorem extendedFabius_eq_globalBinaryReductionSum_add_remainder
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) (N : ℕ) :
    extendedFabius F x =
      (∑ m ∈ Finset.range (N + 1), globalBinaryReductionSummand x m) +
        binaryReductionRemainder F x N := by
  induction N with
  | zero =>
      simpa using
        extendedFabius_eq_globalBinaryReduction_zero_add_remainder F hF x hx0
  | succ N ih =>
      rw [show N + 1 + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ]
      let m := N + 1
      have hm : 1 ≤ m := by simp [m]
      have hpred : m - 1 = N := by simp [m]
      rcases binaryPrefix_eq_double_or_succ x m hm with hzero | hone
      · have htail : binaryTail x N = binaryTail x m := by
          rw [← hpred]
          exact binaryTail_step_zero x m hm hzero
        have hcoeff : globalBinaryReductionCoefficient x m = 0 :=
          globalBinaryReductionCoefficient_of_zero x m hm hzero
        have hsign : binaryWeight (binaryPrefix x m) =
            binaryWeight (binaryPrefix x N) := by
          rw [hzero, binaryWeight_two_mul, hpred]
        rw [ih]
        simp only [globalBinaryReductionSummand, binaryReductionRemainder]
        rw [hcoeff, zero_mul, add_zero, htail, hsign]
      · have htailStep : binaryTail x N =
            (2 : ℝ) ^ (-(m : ℤ)) + binaryTail x m := by
          rw [← hpred]
          exact binaryTail_step_one x m hm hone
        have htail0 : 0 ≤ binaryTail x m := binaryTail_nonneg x m hx0
        have htaillt : binaryTail x m < (2 : ℝ) ^ (-(m : ℤ)) := by
          simpa only [zpow_neg, zpow_natCast] using binaryTail_lt x m
        have harg0 : 0 < binaryTail x N := by
          rw [htailStep]
          positivity
        have hlo : (2 : ℝ) ^ (-(m : ℤ)) ≤ binaryTail x N := by
          rw [htailStep]
          linarith
        have hhi : binaryTail x N < (2 : ℝ) ^ (-(m : ℤ) + 1) := by
          calc
            binaryTail x N =
                (2 : ℝ) ^ (-(m : ℤ)) + binaryTail x m := htailStep
            _ < (2 : ℝ) ^ (-(m : ℤ)) + (2 : ℝ) ^ (-(m : ℤ)) :=
              by linarith
            _ = (2 : ℝ) ^ (-(m : ℤ) + 1) := by
              rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
              norm_num
              ring
        have hreduce := extendedFabius_reduction F hF (binaryTail x N)
          (m : ℤ) harg0 hlo hhi
        have hreduce' : extendedFabius F (binaryTail x N) =
            -extendedFabius F (binaryTail x m) +
              fabiusReductionSum m (binaryTail x m) := by
          simpa only [Int.natCast_nonneg, if_pos, Int.toNat_natCast,
            htailStep, add_sub_cancel_left] using hreduce
        have hcoeff : globalBinaryReductionCoefficient x m =
            (-1 : ℝ) ^ binaryWeight (binaryPrefix x N) := by
          rw [← hpred]
          exact globalBinaryReductionCoefficient_of_one x m hm hone
        have hsign : (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) =
            -((-1 : ℝ) ^ binaryWeight (binaryPrefix x N)) := by
          rw [hone, binaryWeight_two_mul_add_one, pow_succ, hpred]
          ring
        rw [ih]
        simp only [globalBinaryReductionSummand, binaryReductionRemainder]
        rw [hreduce', hcoeff, hsign]
        dsimp only [m]
        ring

/-- All-real finite telescope.  For a nonpositive input the extension,
summands, and residual all vanish termwise. -/
theorem extendedFabius_eq_globalBinaryReductionSum_add_remainder_all
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (N : ℕ) :
    extendedFabius F x =
      (∑ m ∈ Finset.range (N + 1), globalBinaryReductionSummand x m) +
        binaryReductionRemainder F x N := by
  rcases le_total 0 x with hx | hx
  · exact extendedFabius_eq_globalBinaryReductionSum_add_remainder
      F hF x hx N
  · rw [extendedFabius_eq_zero_of_nonpos F hF hx,
      binaryReductionRemainder_eq_zero_of_nonpos F hF N hx]
    simp [globalBinaryReductionSummand_eq_zero_of_nonpos _ hx]

/-- All-real scale-zero telescope, including the trivial nonpositive
branch. -/
theorem extendedFabius_eq_globalBinaryReduction_zero_add_remainder_all
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    extendedFabius F x =
      globalBinaryReductionSummand x 0 + binaryReductionRemainder F x 0 := by
  simpa using
    extendedFabius_eq_globalBinaryReductionSum_add_remainder_all F hF x 0

/-- For nonnegative `x` the binary tails tend to zero as the scale
grows, by squeezing between `0` and `2 ^ (-m)`. -/
theorem binaryTail_tendsto_zero (x : ℝ) (hx0 : 0 ≤ x) :
    Tendsto (binaryTail x) atTop (𝓝 0) := by
  apply squeeze_zero
  · exact fun N ↦ binaryTail_nonneg x N hx0
  · exact fun N ↦ (binaryTail_lt x N).le
  · simpa only [← inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1))

/-- For an `IsFabius` extension and nonnegative `x`, the signed
residual after `N` fractional binary digits tends to zero. -/
theorem binaryReductionRemainder_tendsto_zero
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) :
    Tendsto (binaryReductionRemainder F x) atTop (𝓝 0) := by
  have hE : Tendsto (fun N ↦ extendedFabius F (binaryTail x N)) atTop
      (𝓝 (extendedFabius F 0)) :=
    (extendedFabius_contDiff F hF).continuous.continuousAt.tendsto.comp
      (binaryTail_tendsto_zero x hx0)
  have hE0 : extendedFabius F 0 = 0 :=
    extendedFabius_eq_zero_of_nonpos F hF le_rfl
  rw [hE0] at hE
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hE.norm using 1
  · funext N
    rw [binaryReductionRemainder, norm_mul, norm_pow]
    norm_num
  · norm_num

/-- All-real residual convergence.  The nonpositive branch is identically
zero, while the nonnegative branch follows from convergence of binary tails. -/
theorem binaryReductionRemainder_tendsto_zero_all
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    Tendsto (binaryReductionRemainder F x) atTop (𝓝 0) := by
  rcases le_total 0 x with hx | hx
  · exact binaryReductionRemainder_tendsto_zero F hF x hx
  · have hzero : binaryReductionRemainder F x = fun _ : ℕ => (0 : ℝ) := by
      funext N
      exact binaryReductionRemainder_eq_zero_of_nonpos F hF N hx
    rw [hzero]
    exact tendsto_const_nhds

private lemma fabiusReal_le_two_mul_of_mem_Icc_half
    (F : BoundedFabius) (hF : IsFabius F) (y : ℝ)
    (hy : y ∈ Icc (0 : ℝ) (1 / 2)) :
    fabiusReal F y ≤ 2 * y := by
  have hcont : ContinuousOn (fabiusReal F) (Icc (0 : ℝ) (1 / 2)) :=
    hF.contDiff.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ (fabiusReal F)
      (interior (Icc (0 : ℝ) (1 / 2))) :=
    (hF.contDiff.differentiable (by simp)).differentiableOn
  have hderiv : ∀ z ∈ interior (Icc (0 : ℝ) (1 / 2)),
      deriv (fabiusReal F) z ≤ 2 := by
    intro z hz
    rw [interior_Icc] at hz
    rw [(hF.hasDerivAt z ⟨hz.1.le, hz.2.le⟩).deriv]
    nlinarith [fabiusReal_le_one F (2 * z)]
  have hbound := (convex_Icc (0 : ℝ) (1 / 2)).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff hderiv 0 (by constructor <;> norm_num) y hy hy.1
  rw [hF.zero_of_nonpos 0 le_rfl] at hbound
  linarith

private lemma inverse_two_pow_le_half (N : ℕ) (hN : 1 ≤ N) :
    ((2 : ℝ) ^ N)⁻¹ ≤ 1 / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hden : (2 : ℝ) ≤ 2 * 2 ^ k := by nlinarith
  simpa only [pow_add, pow_one, mul_comm, one_div] using
    inv_anti₀ (by norm_num : (0 : ℝ) < 2) hden

private lemma binaryTail_mem_Icc_half
    (x : ℝ) (hx0 : 0 ≤ x) (N : ℕ) (hN : 1 ≤ N) :
    binaryTail x N ∈ Icc (0 : ℝ) (1 / 2) := by
  exact ⟨binaryTail_nonneg x N hx0,
    (binaryTail_lt x N).le.trans (inverse_two_pow_le_half N hN)⟩

/-- Geometric bound on the residual: for `0 ≤ x` and `1 ≤ N` its
norm is at most `2 * 2 ^ (-N)`.  The hypothesis `1 ≤ N` places the
tail inside `[0, 1/2]`, where `fabiusReal F y ≤ 2 * y`. -/
theorem norm_binaryReductionRemainder_le
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) (N : ℕ) (hN : 1 ≤ N) :
    ‖binaryReductionRemainder F x N‖ ≤
      2 * ((2 : ℝ) ^ N)⁻¹ := by
  have htailHalf := binaryTail_mem_Icc_half x hx0 N hN
  have htailUnit : binaryTail x N ∈ Icc (0 : ℝ) 1 :=
    ⟨htailHalf.1, htailHalf.2.trans (by norm_num)⟩
  have hE := extendedFabius_eq_fabiusReal F hF htailUnit
  rw [binaryReductionRemainder, norm_mul, norm_pow]
  norm_num
  rw [hE, abs_of_nonneg (fabiusReal_nonneg F _)]
  calc
    fabiusReal F (binaryTail x N) ≤ 2 * binaryTail x N :=
      fabiusReal_le_two_mul_of_mem_Icc_half F hF _ htailHalf
    _ ≤ 2 * ((2 : ℝ) ^ N)⁻¹ := by
      nlinarith [(binaryTail_lt x N).le]

/-- All-real residual bound.  The geometric estimate is unchanged on the
nonnegative half-line and is immediate on the nonpositive half-line. -/
theorem norm_binaryReductionRemainder_le_all
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖binaryReductionRemainder F x N‖ ≤
      2 * ((2 : ℝ) ^ N)⁻¹ := by
  rcases le_total 0 x with hx | hx
  · exact norm_binaryReductionRemainder_le F hF x hx N hN
  · rw [binaryReductionRemainder_eq_zero_of_nonpos F hF N hx]
    simp only [norm_zero]
    positivity

/-- The binary-reduction residual satisfies its geometric bound at every
real input and every natural scale, including scale zero. -/
theorem norm_binaryReductionRemainder_le_total
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (N : ℕ) :
    ‖binaryReductionRemainder F x N‖ ≤
      2 * ((2 : ℝ) ^ N)⁻¹ := by
  cases N with
  | zero =>
      rcases le_total 0 x with hx | hx
      · have htailLt : binaryTail x 0 < 1 := by
          simpa using binaryTail_lt x 0
        have htailUnit : binaryTail x 0 ∈ Icc (0 : ℝ) 1 :=
          ⟨binaryTail_nonneg x 0 hx, htailLt.le⟩
        have hE := extendedFabius_eq_fabiusReal F hF htailUnit
        rw [binaryReductionRemainder, norm_mul, norm_pow]
        norm_num
        rw [hE, abs_of_nonneg (fabiusReal_nonneg F _)]
        linarith [fabiusReal_le_one F (binaryTail x 0)]
      · rw [binaryReductionRemainder_eq_zero_of_nonpos F hF 0 hx,
          norm_zero]
        norm_num
  | succ N =>
      exact norm_binaryReductionRemainder_le_all
        F hF x (N + 1) (by omega)

/-- Uniform quantitative error for the finite binary-reduction telescope.
After retaining the scales `0, ..., N`, the error is at most `2 * 2⁻ᴺ`,
independently of the nonnegative input `x`. -/
theorem norm_extendedFabius_sub_globalBinaryReductionSum_le
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) (N : ℕ) (hN : 1 ≤ N) :
    ‖extendedFabius F x -
        ∑ m ∈ Finset.range (N + 1), globalBinaryReductionSummand x m‖ ≤
      2 * ((2 : ℝ) ^ N)⁻¹ := by
  have hrem := norm_binaryReductionRemainder_le F hF x hx0 N hN
  have hid := extendedFabius_eq_globalBinaryReductionSum_add_remainder
    F hF x hx0 N
  rw [hid]
  simpa only [add_sub_cancel_left] using hrem

/-- All-real form of the uniform finite-telescope error.  On nonnegative
inputs it is the residual estimate; on nonpositive inputs both the signed
extension and every finite summand vanish exactly. -/
theorem norm_globalBinaryReductionSum_sub_extendedFabius_le
    (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    ‖(∑ m ∈ Finset.range (N + 1), globalBinaryReductionSummand x m) -
        extendedFabius F x‖ ≤ 2 * ((2 : ℝ) ^ N)⁻¹ := by
  rw [norm_sub_rev]
  have hrem := norm_binaryReductionRemainder_le_all F hF x N hN
  have hid :=
    extendedFabius_eq_globalBinaryReductionSum_add_remainder_all F hF x N
  rw [hid]
  simpa only [add_sub_cancel_left] using hrem

/-- Uniform finite-telescope error at every real input and every natural
scale, including scale zero. -/
theorem norm_globalBinaryReductionSum_sub_extendedFabius_le_total
    (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) (x : ℝ) :
    ‖(∑ m ∈ Finset.range (N + 1), globalBinaryReductionSummand x m) -
        extendedFabius F x‖ ≤ 2 * ((2 : ℝ) ^ N)⁻¹ := by
  rw [norm_sub_rev]
  have hrem := norm_binaryReductionRemainder_le_total F hF x N
  have hid :=
    extendedFabius_eq_globalBinaryReductionSum_add_remainder_all F hF x N
  rw [hid]
  simpa only [add_sub_cancel_left] using hrem

/-- For `0 ≤ x` and `1 ≤ m` the outer summand at scale `m` is
exactly one step of the residual telescope.  Restated for the
concrete Fabius function as `globalFabius_binary_telescope_step`
in `FabiusDiscreteLimitIntegration`. -/
theorem globalBinaryReductionSummand_eq_remainder_sub
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) (m : ℕ) (hm : 1 ≤ m) :
    globalBinaryReductionSummand x m =
      binaryReductionRemainder F x (m - 1) -
        binaryReductionRemainder F x m := by
  have hprev :=
    extendedFabius_eq_globalBinaryReductionSum_add_remainder
      F hF x hx0 (m - 1)
  have hcur :=
    extendedFabius_eq_globalBinaryReductionSum_add_remainder
      F hF x hx0 m
  have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [hsucc] at hprev
  rw [Finset.sum_range_succ] at hcur
  linarith

/-- At every real input, each positive-index summand is exactly one step of the
residual telescope. -/
theorem globalBinaryReductionSummand_eq_remainder_sub_all
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    globalBinaryReductionSummand x m =
      binaryReductionRemainder F x (m - 1) -
        binaryReductionRemainder F x m := by
  have hprev :=
    extendedFabius_eq_globalBinaryReductionSum_add_remainder_all
      F hF x (m - 1)
  have hcur :=
    extendedFabius_eq_globalBinaryReductionSum_add_remainder_all F hF x m
  have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [hsucc] at hprev
  rw [Finset.sum_range_succ] at hcur
  linarith

/-- For `0 ≤ x` and `2 ≤ m` the outer summand has norm at most
`4 * 2 ^ (-(m - 1))`, obtained from the telescope identity and the
residual bound at scales `m - 1` and `m`. -/
theorem norm_globalBinaryReductionSummand_le_ge_two
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) (m : ℕ) (hm : 2 ≤ m) :
    ‖globalBinaryReductionSummand x m‖ ≤
      4 * ((2 : ℝ) ^ (m - 1))⁻¹ := by
  rw [globalBinaryReductionSummand_eq_remainder_sub F hF x hx0 m (by omega)]
  calc
    ‖binaryReductionRemainder F x (m - 1) - binaryReductionRemainder F x m‖ ≤
        ‖binaryReductionRemainder F x (m - 1)‖ +
          ‖binaryReductionRemainder F x m‖ := norm_sub_le _ _
    _ ≤ 2 * ((2 : ℝ) ^ (m - 1))⁻¹ +
          2 * ((2 : ℝ) ^ m)⁻¹ := by
      gcongr
      · exact norm_binaryReductionRemainder_le F hF x hx0 (m - 1) (by omega)
      · exact norm_binaryReductionRemainder_le F hF x hx0 m (by omega)
    _ ≤ 4 * ((2 : ℝ) ^ (m - 1))⁻¹ := by
      have hpow : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by
        calc
          (2 : ℝ) ^ m = 2 ^ ((m - 1) + 1) := by
            rw [Nat.sub_add_cancel (by omega)]
          _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
      rw [hpow, mul_inv]
      have hnonneg : 0 ≤ ((2 : ℝ) ^ (m - 1))⁻¹ := by positivity
      norm_num
      linarith

/-- At every real input, each positive-index binary-reduction summand has the
geometric majorant `4 * 2⁻⁽ᵐ⁻¹⁾`. -/
theorem norm_globalBinaryReductionSummand_le_of_one_le_all
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ‖globalBinaryReductionSummand x m‖ ≤
      4 * ((2 : ℝ) ^ (m - 1))⁻¹ := by
  rw [globalBinaryReductionSummand_eq_remainder_sub_all F hF x m hm]
  calc
    ‖binaryReductionRemainder F x (m - 1) -
        binaryReductionRemainder F x m‖ ≤
        ‖binaryReductionRemainder F x (m - 1)‖ +
          ‖binaryReductionRemainder F x m‖ := norm_sub_le _ _
    _ ≤ 2 * ((2 : ℝ) ^ (m - 1))⁻¹ +
          2 * ((2 : ℝ) ^ m)⁻¹ := by
      gcongr
      · exact norm_binaryReductionRemainder_le_total F hF x (m - 1)
      · exact norm_binaryReductionRemainder_le_total F hF x m
    _ ≤ 4 * ((2 : ℝ) ^ (m - 1))⁻¹ := by
      have hpow : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by
        calc
          (2 : ℝ) ^ m = 2 ^ ((m - 1) + 1) := by
            rw [Nat.sub_add_cancel hm]
          _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
      rw [hpow, mul_inv]
      have hnonneg : 0 ≤ ((2 : ℝ) ^ (m - 1))⁻¹ := by positivity
      norm_num
      linarith

/-- For nonnegative `x` the outer series converges absolutely, by
comparison with a geometric series after discarding the first two
terms.  Also used in `FabiusGlobalQBinomialSeries` to prove
`summable_norm_qBinomialFabiusGlobalSummand`. -/
theorem summable_norm_globalBinaryReductionSummand
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) :
    Summable (fun m : ℕ ↦ ‖globalBinaryReductionSummand x m‖) := by
  rw [← summable_nat_add_iff (f := fun m : ℕ ↦
    ‖globalBinaryReductionSummand x m‖) 2]
  refine ((summable_geometric_of_norm_lt_one
      (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)).mul_left 4).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) ?_
  intro j
  calc
    ‖globalBinaryReductionSummand x (j + 2)‖ ≤
        4 * ((2 : ℝ) ^ (j + 2 - 1))⁻¹ :=
      norm_globalBinaryReductionSummand_le_ge_two F hF x hx0 (j + 2) (by omega)
    _ ≤ 4 * ((2 : ℝ)⁻¹) ^ j := by
      rw [show j + 2 - 1 = j + 1 by omega, pow_succ, mul_inv]
      rw [inv_pow]
      have hnonneg : 0 ≤ ((2 : ℝ)⁻¹) ^ j := by positivity
      norm_num

/-- Summability of the outer series for nonnegative `x`, deduced
from absolute summability. -/
theorem summable_globalBinaryReductionSummand
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) :
    Summable (globalBinaryReductionSummand x) :=
  Summable.of_norm (summable_norm_globalBinaryReductionSummand F hF x hx0)

/-- The binary-reduction summands are absolutely summable at every real
input.  The geometric comparison starts at the first positive index. -/
theorem summable_norm_globalBinaryReductionSummand_all
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    Summable (fun m : ℕ ↦ ‖globalBinaryReductionSummand x m‖) := by
  rw [← summable_nat_add_iff (f := fun m : ℕ ↦
    ‖globalBinaryReductionSummand x m‖) 1]
  refine ((summable_geometric_of_norm_lt_one
      (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)).mul_left 4).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) ?_
  intro j
  calc
    ‖globalBinaryReductionSummand x (j + 1)‖ ≤
        4 * ((2 : ℝ) ^ (j + 1 - 1))⁻¹ :=
      norm_globalBinaryReductionSummand_le_of_one_le_all
        F hF x (j + 1) (by omega)
    _ = 4 * ((2 : ℝ)⁻¹) ^ j := by
      rw [show j + 1 - 1 = j by omega, inv_pow]

/-- The binary-reduction series is summable at every real input. -/
theorem summable_globalBinaryReductionSummand_all
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    Summable (globalBinaryReductionSummand x) :=
  Summable.of_norm (summable_norm_globalBinaryReductionSummand_all F hF x)

/-- For nonnegative `x` the partial sums over `Finset.range N`
converge to `extendedFabius F x`.  Restated for the concrete
Fabius function as `binary_telescope_tendsto_globalFabius` in
`FabiusDiscreteLimitIntegration`. -/
theorem tendsto_sum_range_globalBinaryReduction
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) :
    Tendsto (fun N : ℕ ↦
      ∑ m ∈ Finset.range N, globalBinaryReductionSummand x m)
      atTop (𝓝 (extendedFabius F x)) := by
  have hrem := binaryReductionRemainder_tendsto_zero F hF x hx0
  have hid := fun N ↦
    extendedFabius_eq_globalBinaryReductionSum_add_remainder F hF x hx0 N
  have ht : Tendsto (fun N : ℕ ↦
      extendedFabius F x - binaryReductionRemainder F x N) atTop
      (𝓝 (extendedFabius F x - 0)) :=
    tendsto_const_nhds.sub hrem
  have hshift : Tendsto (fun N : ℕ ↦
      ∑ m ∈ Finset.range (N + 1), globalBinaryReductionSummand x m)
      atTop (𝓝 (extendedFabius F x)) := by
    have ht' : Tendsto (fun N : ℕ ↦
        extendedFabius F x - binaryReductionRemainder F x N) atTop
        (𝓝 (extendedFabius F x)) := by simpa using ht
    apply ht'.congr'
    filter_upwards with N
    linarith [hid N]
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- The finite binary-reduction telescopes converge uniformly on the whole
real line to the signed extension.  On the nonnegative half-line the residual
bound is independent of `x`; on the nonpositive half-line the approximation
is exact at every scale. -/
theorem globalBinaryReductionSum_tendstoUniformly_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) :
    TendstoUniformly
      (fun N : ℕ => fun x : ℝ =>
        ∑ m ∈ Finset.range (N + 1), globalBinaryReductionSummand x m)
      (extendedFabius F) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hgeom : Tendsto (fun N : ℕ => 2 * ((2 : ℝ) ^ N)⁻¹)
      atTop (𝓝 0) := by
    have hhalf : Tendsto (fun N : ℕ => ((2 : ℝ)⁻¹) ^ N)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)
    simpa only [inv_pow, mul_zero] using tendsto_const_nhds.mul hhalf
  have heps : ∀ᶠ N : ℕ in atTop, 2 * ((2 : ℝ) ^ N)⁻¹ < ε :=
    (tendsto_order.1 hgeom).2 ε hε
  filter_upwards [heps] with N hbound
  intro x
  exact lt_of_le_of_lt
    (by simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using
      norm_globalBinaryReductionSum_sub_extendedFabius_le_total F hF N x)
    hbound

/-- All-real core of the corrected binary-reduction series.  Absolute
summability handles nonnegative inputs, while at a nonpositive input every
summand and the signed extension vanish exactly. -/
theorem hasSum_globalBinaryReductionSummand_all
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasSum (globalBinaryReductionSummand x) (extendedFabius F x) := by
  rcases le_total 0 x with hx0 | hx0
  · rw [hasSum_iff_tendsto_nat_of_summable_norm
      (summable_norm_globalBinaryReductionSummand F hF x hx0)]
    exact tendsto_sum_range_globalBinaryReduction F hF x hx0
  · have hsummand :
        globalBinaryReductionSummand x = fun _ : ℕ => (0 : ℝ) := by
      funext m
      exact globalBinaryReductionSummand_eq_zero_of_nonpos m hx0
    rw [hsummand, extendedFabius_eq_zero_of_nonpos F hF hx0]
    exact hasSum_zero

/-- Compatibility form of the corrected global binary-reduction series on
the nonnegative half-line. -/
theorem hasSum_globalBinaryReductionSummand
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) :
    HasSum (globalBinaryReductionSummand x) (extendedFabius F x) := by
  simpa only [max_eq_right hx0] using
    hasSum_globalBinaryReductionSummand_all F hF (max 0 x)

/-- All-real `tsum` form of the corrected global binary-reduction series. -/
theorem extendedFabius_eq_tsum_globalBinaryReductionSummand_all
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    extendedFabius F x = ∑' m : ℕ, globalBinaryReductionSummand x m :=
  (hasSum_globalBinaryReductionSummand_all F hF x).tsum_eq.symm

/-- Compatibility `tsum` form on the nonnegative half-line. -/
theorem extendedFabius_eq_tsum_globalBinaryReductionSummand
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) :
    extendedFabius F x = ∑' m : ℕ, globalBinaryReductionSummand x m := by
  simpa only [max_eq_right hx0] using
    extendedFabius_eq_tsum_globalBinaryReductionSummand_all
      F hF (max 0 x)

/-- On the original half-open unit interval, the newly restored scale-zero
term vanishes. -/
@[simp] theorem globalBinaryReductionSummand_zero_of_lt_one
    (x : ℝ) (hx : x < 1) :
    globalBinaryReductionSummand x 0 = 0 := by
  have hxhalf : x / 2 < 1 := by linarith
  simp [globalBinaryReductionSummand, globalBinaryReductionCoefficient,
    binaryPreviousPrefix, binaryPrefix, Nat.floor_eq_zero.mpr hx,
    Nat.floor_eq_zero.mpr hxhalf]

/-- The shifted series has the same sum whenever its omitted scale-zero term
vanishes.  This is the common boundary lemma behind the interval-specific
forms below. -/
theorem hasSum_globalBinaryReductionSummand_succ_of_zero
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ)
    (hzero : globalBinaryReductionSummand x 0 = 0) :
    HasSum (fun m : ℕ ↦ globalBinaryReductionSummand x (m + 1))
      (extendedFabius F x) := by
  have h := hasSum_globalBinaryReductionSummand_all F hF x
  have htail := (hasSum_nat_add_iff' (f := globalBinaryReductionSummand x)
    (g := extendedFabius F x) 1).2 h
  simpa [hzero] using htail

/-- `tsum` form of omitting a vanishing scale-zero term. -/
theorem extendedFabius_eq_tsum_globalBinaryReductionSummand_succ_of_zero
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ)
    (hzero : globalBinaryReductionSummand x 0 = 0) :
    extendedFabius F x =
      ∑' m : ℕ, globalBinaryReductionSummand x (m + 1) :=
  (hasSum_globalBinaryReductionSummand_succ_of_zero
    F hF x hzero).tsum_eq.symm

/-- All-real shifted series on the convenient domain `x < 1`, where the
scale-zero summand vanishes. -/
theorem hasSum_globalBinaryReductionSummand_succ_all
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx1 : x < 1) :
    HasSum (fun m : ℕ ↦ globalBinaryReductionSummand x (m + 1))
      (extendedFabius F x) := by
  exact hasSum_globalBinaryReductionSummand_succ_of_zero F hF x
    (globalBinaryReductionSummand_zero_of_lt_one x hx1)

/-- At the right endpoint `x = 1`, the restored scale-zero term is exactly
the missing unit contribution.  This theorem is deliberately not a simp rule;
the existing literal q-binomial endpoint wrapper retains that role. -/
theorem globalBinaryReductionSummand_one_zero :
    globalBinaryReductionSummand 1 0 = 1 := by
  norm_num [globalBinaryReductionSummand, globalBinaryReductionCoefficient,
    binaryPrefix, binaryPreviousPrefix, binaryTail, fabiusReductionSum,
    binaryWeight, halfMoment]

set_option linter.unusedVariables false in
/-- The original `m = 1,2,...` series is valid on `0 ≤ x < 1`.  The now
redundant nonnegativity hypothesis is retained for source compatibility. -/
theorem hasSum_globalBinaryReductionSummand_succ
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun m : ℕ ↦ globalBinaryReductionSummand x (m + 1))
      (extendedFabius F x) := by
  exact hasSum_globalBinaryReductionSummand_succ_all F hF x hx1

/-- `tsum` form of the shifted all-real series on `x < 1`. -/
theorem extendedFabius_eq_tsum_globalBinaryReductionSummand_succ_all
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx1 : x < 1) :
    extendedFabius F x =
      ∑' m : ℕ, globalBinaryReductionSummand x (m + 1) :=
  (hasSum_globalBinaryReductionSummand_succ_all F hF x hx1).tsum_eq.symm

set_option linter.unusedVariables false in
/-- `tsum` form of the shifted `m = 1, 2, ...` series, valid on
`0 ≤ x < 1`, where the scale-zero term vanishes.  The nonnegativity binder is
retained for source compatibility with the original theorem. -/
theorem extendedFabius_eq_tsum_globalBinaryReductionSummand_succ
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    extendedFabius F x =
      ∑' m : ℕ, globalBinaryReductionSummand x (m + 1) :=
  extendedFabius_eq_tsum_globalBinaryReductionSummand_succ_all F hF x hx1

/-- Bounded-function form on the closed unit interval. -/
theorem hasSum_fabiusReal_globalBinaryReductionSummand
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (globalBinaryReductionSummand x) (fabiusReal F x) := by
  rw [← extendedFabius_eq_fabiusReal F hF hx]
  exact hasSum_globalBinaryReductionSummand F hF x hx.1

/-- `tsum` form on the closed unit interval `[0, 1]`, stated for the
bounded function `fabiusReal F` instead of the signed global
extension. -/
theorem fabiusReal_eq_tsum_globalBinaryReductionSummand
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusReal F x = ∑' m : ℕ, globalBinaryReductionSummand x m :=
  (hasSum_fabiusReal_globalBinaryReductionSummand F hF x hx).tsum_eq.symm

end

end Fabius
