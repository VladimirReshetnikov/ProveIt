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
extension for every real input: on the nonpositive half-line both sides
vanish termwise.  Its summands are absolutely summable on the whole real
line.  The established theorem signatures with `0 ≤ x` are kept as wrappers.
The original series starting at `m = 1` remains valid on the full domain
`x < 1`; its nonpositive branch is identically zero.
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

/-- The half-difference of a parity sign is the signed low binary digit,
written as the exact natural quotient expression used by the global
coefficient. -/
theorem neg_one_pow_sub_one_half (a : ℕ) :
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

/-- Exact coefficient bridge between the source-literal parity factors and
the analytic binary-reduction coefficient.  It is valid at every scale,
including the half-scale convention at `m = 0`. -/
theorem fabiusParityPowerCoefficient_eq_globalBinaryReductionCoefficient
    (x : ℝ) (m : ℕ) :
    (((-1 : ℝ) ^ binaryPrefix x m) - 1) *
        (-1 : ℝ) ^ thueMorseBit (binaryPrefix x m) * (1 / 2 : ℝ) =
      globalBinaryReductionCoefficient x m := by
  have hprev := binaryPreviousPrefix_eq_binaryPrefix_div_two x m
  have hparity := neg_one_pow_sub_one_half (binaryPrefix x m)
  rw [neg_one_pow_thueMorseBit_eq_binaryWeight,
    globalBinaryReductionCoefficient]
  calc
    (((-1 : ℝ) ^ binaryPrefix x m - 1) *
          (-1 : ℝ) ^ binaryWeight (binaryPrefix x m)) * (1 / 2 : ℝ) =
        (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) *
          ((((-1 : ℝ) ^ binaryPrefix x m - 1) * (1 / 2 : ℝ))) := by
      ring
    _ = (-1 : ℝ) ^ binaryWeight (binaryPrefix x m) *
          (2 * (binaryPreviousPrefix x m : ℝ) -
            (binaryPrefix x m : ℝ)) := by
      rw [hparity, hprev]

/-- Pointwise bridge from the parity-power formula to the analytic binary
reduction summand. -/
theorem fabiusParityPowerSummand_eq_globalBinaryReductionSummand
    (x : ℝ) (m : ℕ) :
    fabiusParityPowerSummand x m = globalBinaryReductionSummand x m := by
  rw [fabiusParityPowerSummand,
    fabiusParityPowerInner_eq_half_reductionSum,
    globalBinaryReductionSummand]
  calc
    _ = ((((-1 : ℝ) ^ binaryPrefix x m) - 1) *
            (-1 : ℝ) ^ thueMorseBit (binaryPrefix x m)) *
            (1 / 2 : ℝ) *
          fabiusReductionSum m (binaryTail x m) := by ring
    _ = globalBinaryReductionCoefficient x m *
          fabiusReductionSum m (binaryTail x m) := by
      rw [fabiusParityPowerCoefficient_eq_globalBinaryReductionCoefficient]

/-- Every parity-power summand vanishes termwise on the nonpositive
half-line. -/
@[simp] theorem fabiusParityPowerSummand_eq_zero_of_nonpos
    (m : ℕ) {x : ℝ} (hx : x ≤ 0) :
    fabiusParityPowerSummand x m = 0 := by
  rw [fabiusParityPowerSummand_eq_globalBinaryReductionSummand,
    globalBinaryReductionSummand_eq_zero_of_nonpos m hx]

/-- On the original half-open unit interval, the scale-zero parity-power
summand vanishes pointwise. -/
theorem fabiusParityPowerSummand_zero_of_lt_one (x : ℝ) (hx : x < 1) :
    fabiusParityPowerSummand x 0 = 0 := by
  rw [fabiusParityPowerSummand_eq_globalBinaryReductionSummand,
    globalBinaryReductionSummand_zero_of_lt_one x hx]

/-- At `x = 1`, the restored scale-zero parity-power term is exactly one. -/
theorem fabiusParityPowerSummand_one_zero :
    fabiusParityPowerSummand 1 0 = 1 := by
  rw [fabiusParityPowerSummand_eq_globalBinaryReductionSummand,
    globalBinaryReductionSummand_one_zero]

/-- The corrected parity-power summands are absolutely summable at every real
input. -/
theorem summable_norm_fabiusParityPowerSummand_all (x : ℝ) :
    Summable (fun m : ℕ => ‖fabiusParityPowerSummand x m‖) := by
  exact (summable_norm_globalBinaryReductionSummand_all
    fabius fabius_spec x).congr
      (fun m => by
        rw [fabiusParityPowerSummand_eq_globalBinaryReductionSummand])

/-- Compatibility form of absolute summability on nonnegative inputs. -/
theorem summable_norm_fabiusParityPowerSummand
    (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun m : ℕ => ‖fabiusParityPowerSummand x m‖) := by
  simpa only [max_eq_left hx] using
    summable_norm_fabiusParityPowerSummand_all (max x 0)

/-- All-real core of the corrected parity-power series, starting at `m = 0`.
On nonpositive inputs it is the zero series. -/
theorem hasSum_fabiusParityPowerSummand_all (x : ℝ) :
    HasSum (fabiusParityPowerSummand x) (globalFabius x) := by
  exact (hasSum_globalBinaryReductionSummand_all
    fabius fabius_spec x).congr_fun
      (fun m => fabiusParityPowerSummand_eq_globalBinaryReductionSummand x m)

/-- Compatibility form of the corrected global series on `x ≥ 0`. -/
theorem hasSum_fabiusParityPowerSummand
    (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fabiusParityPowerSummand x) (globalFabius x) := by
  simpa only [max_eq_left hx] using
    hasSum_fabiusParityPowerSummand_all (max x 0)

/-- All-real `tsum` form of the corrected `m = 0,1,...` series. -/
theorem globalFabius_eq_tsum_fabiusParityPowerSummand_all (x : ℝ) :
    globalFabius x = ∑' m : ℕ, fabiusParityPowerSummand x m :=
  (hasSum_fabiusParityPowerSummand_all x).tsum_eq.symm

/-- Compatibility `tsum` form for every `x ≥ 0`. -/
theorem globalFabius_eq_tsum_fabiusParityPowerSummand
    (x : ℝ) (hx : 0 ≤ x) :
    globalFabius x = ∑' m : ℕ, fabiusParityPowerSummand x m := by
  simpa only [max_eq_left hx] using
    globalFabius_eq_tsum_fabiusParityPowerSummand_all (max x 0)

/-- Fully expanded all-real parity-power formula.  The outer series starts at
`m = 0`, the quadratic exponent is interpreted using integer division, and
the binary tail is displayed literally. -/
theorem globalFabius_eq_tsum_fabiusParityPower_literal_all (x : ℝ) :
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
  rw [globalFabius_eq_tsum_fabiusParityPowerSummand_all x]
  apply tsum_congr
  intro m
  rw [fabiusParityPowerSummand, fabiusParityPowerInner,
    binaryTail, binaryPrefix]
  simp_rw [fabiusParityPowerExponent_eq_choose_sub_one]

set_option linter.unusedVariables false in
/-- Compatibility form of the fully expanded formula on `x ≥ 0`; the
nonnegativity binder is retained for source compatibility. -/
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
  exact globalFabius_eq_tsum_fabiusParityPower_literal_all x

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

/-- The shifted series has the same sum whenever its omitted scale-zero term
vanishes. -/
theorem hasSum_fabiusParityPowerSummand_succ_of_zero
    (x : ℝ) (hzero : fabiusParityPowerSummand x 0 = 0) :
    HasSum (fun m : ℕ => fabiusParityPowerSummand x (m + 1))
      (globalFabius x) := by
  have hglobalzero : globalBinaryReductionSummand x 0 = 0 := by
    simpa only [fabiusParityPowerSummand_eq_globalBinaryReductionSummand]
      using hzero
  exact (hasSum_globalBinaryReductionSummand_succ_of_zero
    fabius fabius_spec x hglobalzero).congr_fun
      (fun m => fabiusParityPowerSummand_eq_globalBinaryReductionSummand
        x (m + 1))

/-- `tsum` form of omitting a vanishing scale-zero parity-power term. -/
theorem globalFabius_eq_tsum_fabiusParityPowerSummand_succ_of_zero
    (x : ℝ) (hzero : fabiusParityPowerSummand x 0 = 0) :
    globalFabius x =
      ∑' m : ℕ, fabiusParityPowerSummand x (m + 1) :=
  (hasSum_fabiusParityPowerSummand_succ_of_zero x hzero).tsum_eq.symm

/-- The shifted series starting at `m = 1` is valid for every `x < 1`;
nonpositive inputs contribute the zero series. -/
theorem hasSum_fabiusParityPowerSummand_succ_all
    (x : ℝ) (hx1 : x < 1) :
    HasSum (fun m : ℕ => fabiusParityPowerSummand x (m + 1))
      (globalFabius x) := by
  exact hasSum_fabiusParityPowerSummand_succ_of_zero x
    (fabiusParityPowerSummand_zero_of_lt_one x hx1)

set_option linter.unusedVariables false in
/-- Compatibility form of the shifted series on `0 ≤ x < 1`; the
nonnegativity binder is retained for source compatibility. -/
theorem hasSum_fabiusParityPowerSummand_succ
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun m : ℕ => fabiusParityPowerSummand x (m + 1))
      (globalFabius x) := by
  exact hasSum_fabiusParityPowerSummand_succ_all x hx1

/-- `tsum` form of the shifted parity-power series on every `x < 1`. -/
theorem globalFabius_eq_tsum_fabiusParityPowerSummand_succ_all
    (x : ℝ) (hx1 : x < 1) :
    globalFabius x =
      ∑' m : ℕ, fabiusParityPowerSummand x (m + 1) :=
  (hasSum_fabiusParityPowerSummand_succ_all x hx1).tsum_eq.symm

set_option linter.unusedVariables false in
/-- `tsum` form of the original `m = 1,2,...` theorem on `0 ≤ x < 1`; the
nonnegativity binder is retained for source compatibility. -/
theorem globalFabius_eq_tsum_fabiusParityPowerSummand_succ
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    globalFabius x =
      ∑' m : ℕ, fabiusParityPowerSummand x (m + 1) :=
  globalFabius_eq_tsum_fabiusParityPowerSummand_succ_all x hx1

end

end Fabius
