import FabiusFunction.AnalyticMoments
import FabiusFunction.FabiusBinaryReductionSeries
import FabiusFunction.PaperStatements
import FabiusFunction.ThueMorseBinomialLog

/-!
# The parity-power global Fabius series

This file formalizes the corrected scale-zero version of the proposed series.
The exponent is an integer exponent, so its value at `n = 0` is genuinely
`-1`. Lean's convention `0 ^ 0 = 1` is used in the polynomial term.

The corrected series starts at `m = 0` and equals the signed global Fabius
extension for every nonnegative real input. The original series starting at
`m = 1` remains valid on the half-open unit interval `0 ≤ x < 1`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

noncomputable section

/-- The user's quadratic exponent is the triangular exponent minus one.
Integer division is essential here: both sides equal `-1` when `n = 0`. -/
theorem fabiusParityPowerExponent_eq_choose_sub_one (n : ℕ) :
    (((n : ℤ) + 2) * ((n : ℤ) - 1)) / 2 =
      (Nat.choose (n + 1) 2 : ℤ) - 1 := by
  have hc := congrArg (fun k : ℕ => (k : ℤ))
    (two_mul_choose_succ_two n)
  push_cast at hc
  have hnum :
      ((n : ℤ) + 2) * ((n : ℤ) - 1) =
        2 * ((Nat.choose (n + 1) 2 : ℤ) - 1) := by
    linarith
  rw [hnum]
  omega

/-- The literal finite inner sum in the parity-power formula. -/
def fabiusParityPowerInner (m : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1),
    (2 : ℝ) ^ ((Nat.choose (n + 1) 2 : ℤ) - 1) *
      globalFabius ((2 : ℝ) ^ ((n : ℤ) - (m : ℤ))) *
      y ^ n / (n.factorial : ℝ)

private theorem globalFabius_two_zpow_sub
    (m n : ℕ) (hn : n ≤ m) :
    globalFabius ((2 : ℝ) ^ ((n : ℤ) - (m : ℤ))) =
      (halfMoment (m - n) : ℝ) /
        (((m - n).factorial : ℝ) *
          (2 : ℝ) ^ Nat.choose (m - n) 2) := by
  let d := m - n
  have hexp : (n : ℤ) - (m : ℤ) = -(d : ℤ) := by
    dsimp only [d]
    omega
  have harg :
      (2 : ℝ) ^ ((n : ℤ) - (m : ℤ)) = ((2 : ℝ) ^ d)⁻¹ := by
    rw [hexp, zpow_neg, zpow_natCast]
  have hmem : ((2 : ℝ) ^ d)⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [harg, globalFabius,
    extendedFabius_eq_fabiusReal fabius fabius_spec hmem]
  have hmoment := halfMoment_eq_fabius_formula fabius fabius_spec d
  have hden :
      (((d.factorial : ℝ) * (2 : ℝ) ^ Nat.choose d 2)) ≠ 0 := by
    positivity
  rw [eq_div_iff hden]
  nlinarith

/-- The user's inner sum is exactly half of the Taylor reduction polynomial. -/
theorem fabiusParityPowerInner_eq_half_reductionSum (m : ℕ) (y : ℝ) :
    fabiusParityPowerInner m y =
      (1 / 2 : ℝ) * fabiusReductionSum m y := by
  rw [fabiusParityPowerInner, fabiusReductionSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    simpa using Finset.mem_range.mp hn
  rw [globalFabius_two_zpow_sub m n hnm]
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num only [zpow_natCast, zpow_one]
  field_simp [Nat.cast_ne_zero]

private theorem neg_one_pow_sub_one_half (a : ℕ) :
    (((-1 : ℝ) ^ a - 1) * (1 / 2 : ℝ)) =
      2 * (a / 2 : ℕ) - (a : ℝ) := by
  have hmod : a % 2 < 2 := Nat.mod_lt a (by omega)
  have hdecomp := (Nat.mod_add_div a 2).symm
  interval_cases h : a % 2
  · have ha : a = 2 * (a / 2) := by omega
    have haR : (a : ℝ) = 2 * (a / 2 : ℕ) := by exact_mod_cast ha
    calc
      (((-1 : ℝ) ^ a - 1) * (1 / 2 : ℝ)) = 0 := by
        rw [ha, pow_mul]
        norm_num
      _ = 2 * (a / 2 : ℕ) - (a : ℝ) := by rw [haR]; ring
  · have ha : a = 2 * (a / 2) + 1 := by omega
    have haR : (a : ℝ) = 2 * (a / 2 : ℕ) + 1 := by exact_mod_cast ha
    calc
      (((-1 : ℝ) ^ a - 1) * (1 / 2 : ℝ)) = -1 := by
        rw [ha, pow_add, pow_mul]
        norm_num
      _ = 2 * (a / 2 : ℕ) - (a : ℝ) := by rw [haR]; ring

/-- The literal outer summand proposed by the user, with corrected scale-zero
semantics inherited from `binaryPrefix` and `binaryTail`. -/
def fabiusParityPowerSummand (x : ℝ) (m : ℕ) : ℝ :=
  (((-1 : ℝ) ^ binaryPrefix x m) - 1) *
    (-1 : ℝ) ^ thueMorseBit (binaryPrefix x m) *
    fabiusParityPowerInner m (binaryTail x m)

/-- Pointwise bridge from the parity-power formula to the analytic binary
reduction summand. -/
theorem fabiusParityPowerSummand_eq_globalBinaryReductionSummand
    (x : ℝ) (m : ℕ) :
    fabiusParityPowerSummand x m = globalBinaryReductionSummand x m := by
  rw [fabiusParityPowerSummand,
    fabiusParityPowerInner_eq_half_reductionSum,
    globalBinaryReductionSummand, globalBinaryReductionCoefficient]
  have hprev := binaryPreviousPrefix_eq_binaryPrefix_div_two x m
  have hparity := neg_one_pow_sub_one_half (binaryPrefix x m)
  have hsign :
      (-1 : ℝ) ^ thueMorseBit (binaryPrefix x m) =
        (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) := by
    rw [thueMorseBit]
    exact (neg_one_pow_eq_pow_mod_two
      (R := ℝ) (binaryWeight (binaryPrefix x m))).symm
  rw [hsign]
  calc
    (((-1 : ℝ) ^ binaryPrefix x m - 1) *
          (-1 : ℝ) ^ binaryWeight (binaryPrefix x m)) *
          ((1 / 2 : ℝ) * fabiusReductionSum m (binaryTail x m)) =
        (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) *
          ((((-1 : ℝ) ^ binaryPrefix x m - 1) * (1 / 2 : ℝ))) *
          fabiusReductionSum m (binaryTail x m) := by ring
    _ = (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) *
          (2 * (binaryPreviousPrefix x m : ℝ) -
            (binaryPrefix x m : ℝ)) *
          fabiusReductionSum m (binaryTail x m) := by
      rw [hparity, hprev]

/-- Corrected global series, starting at `m = 0`, for every `x ≥ 0`. -/
theorem hasSum_fabiusParityPowerSummand
    (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fabiusParityPowerSummand x) (globalFabius x) := by
  exact (hasSum_globalBinaryReductionSummand
    fabius fabius_spec x hx).congr_fun
      (fun m => fabiusParityPowerSummand_eq_globalBinaryReductionSummand x m)

/-- `tsum` form of the corrected `m = 0,1,...` series for every `x ≥ 0`. -/
theorem globalFabius_eq_tsum_fabiusParityPowerSummand
    (x : ℝ) (hx : 0 ≤ x) :
    globalFabius x = ∑' m : ℕ, fabiusParityPowerSummand x m :=
  (hasSum_fabiusParityPowerSummand x hx).tsum_eq.symm

/-- Fully expanded corrected parity-power formula. The outer series starts at
`m = 0`, the quadratic exponent is interpreted using integer division, and
the binary tail is displayed literally. -/
theorem globalFabius_eq_tsum_fabiusParityPower_literal
    (x : ℝ) (hx : 0 ≤ x) :
    globalFabius x =
      ∑' m : ℕ,
        (((-1 : ℝ) ^ ⌊(2 : ℝ) ^ m * x⌋₊) - 1) *
          (-1 : ℝ) ^ thueMorseBit ⌊(2 : ℝ) ^ m * x⌋₊ *
          (∑ n ∈ Finset.range (m + 1),
            (2 : ℝ) ^
                ((((n : ℤ) + 2) * ((n : ℤ) - 1)) / 2) *
              globalFabius
                ((2 : ℝ) ^ ((n : ℤ) - (m : ℤ))) *
              (x - (⌊(2 : ℝ) ^ m * x⌋₊ : ℝ) /
                (2 : ℝ) ^ m) ^ n /
              (n.factorial : ℝ)) := by
  rw [globalFabius_eq_tsum_fabiusParityPowerSummand x hx]
  apply tsum_congr
  intro m
  rw [fabiusParityPowerSummand, fabiusParityPowerInner,
    binaryTail, binaryPrefix]
  simp_rw [fabiusParityPowerExponent_eq_choose_sub_one]

/-- On `[0,1]`, the corrected series has the ordinary bounded Fabius function
as its sum. -/
theorem hasSum_fabiusReal_fabiusParityPowerSummand
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fabiusParityPowerSummand x) (fabiusReal fabius x) := by
  rw [← extendedFabius_eq_fabiusReal fabius fabius_spec hx]
  simpa only [globalFabius] using hasSum_fabiusParityPowerSummand x hx.1

/-- `tsum` form of the bounded `[0,1]` parity-power formula. -/
theorem fabiusReal_eq_tsum_fabiusParityPowerSummand
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    fabiusReal fabius x = ∑' m : ℕ, fabiusParityPowerSummand x m :=
  (hasSum_fabiusReal_fabiusParityPowerSummand x hx).tsum_eq.symm

/-- The original series starting at `m = 1` is valid on `0 ≤ x < 1`. -/
theorem hasSum_fabiusParityPowerSummand_succ
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun m : ℕ => fabiusParityPowerSummand x (m + 1))
      (globalFabius x) := by
  exact (hasSum_globalBinaryReductionSummand_succ
    fabius fabius_spec x hx0 hx1).congr_fun
      (fun m => fabiusParityPowerSummand_eq_globalBinaryReductionSummand
        x (m + 1))

/-- `tsum` form of the original `m = 1,2,...` theorem on `0 ≤ x < 1`. -/
theorem globalFabius_eq_tsum_fabiusParityPowerSummand_succ
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    globalFabius x =
      ∑' m : ℕ, fabiusParityPowerSummand x (m + 1) :=
  (hasSum_fabiusParityPowerSummand_succ x hx0 hx1).tsum_eq.symm

end

end Fabius
