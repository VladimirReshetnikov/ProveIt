import FabiusFunction.FabiusBinaryReductionSeries
import FabiusFunction.FabiusQBinomialTaylor

/-!
# The global q-binomial--Thue--Morse Fabius series

This module combines the constant-polynomial identity from
`FabiusQBinomialTaylor` with the absolutely convergent binary telescope from
`FabiusBinaryReductionSeries`.

The resulting source-literal summand is valid over both `ℝ` and `ℂ`.  For
every real `x ≥ 0` and every real or complex translation `q`, its series sums
to the signed global Fabius extension.  On `[0,1]`, this is the usual bounded
Fabius function.  The scale-zero term uses `Floor[x / 2]`; it is precisely the
term missing from the version indexed from one.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

noncomputable section

/-- The literal nested summand in the Wolfram formula, interpreted in either
`ℝ` or `ℂ`.  Natural powers use Lean's convention `0 ^ 0 = 1`. -/
def qBinomialFabiusGlobalSummand
    (K : Type*) [RCLike K] (q : K) (x : ℝ) (m : ℕ) : K :=
  (-1 : K) ^ thueMorseBit (binaryPrefix x m) *
    (2 * (binaryPreviousPrefix x m : K) - (binaryPrefix x m : K)) *
    ((∑ n ∈ Finset.range (m + 1),
        (((((2 : ℝ) ^ (m + 1) * x -
                2 * (binaryPrefix x m : ℝ) : ℝ) : K) ^ (m - n) /
            ((m - n).factorial : K)) *
          ((∑ k ∈ Finset.range (n + 1),
              algebraMap ℚ K
                (qBinomial n k (1 / 2) /
                  ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
                ∑ r ∈ Finset.range (2 ^ k),
                  (-1 : K) ^ thueMorseBit r *
                    ((r : K) - (2 : K) ^ k + q) ^ (n + k)) /
            algebraMap ℚ K
              ((2 : ℚ) ^ n.choose 2 * qPochhammer (1 / 2) (1 / 2) n)))) /
      (2 : K) ^ (m + 1).choose 2)

private theorem globalBinaryReductionCoefficient_cast
    (K : Type*) [RCLike K] (x : ℝ) (m : ℕ) :
    (globalBinaryReductionCoefficient x m : K) =
      (-1 : K) ^ thueMorseBit (binaryPrefix x m) *
        (2 * (binaryPreviousPrefix x m : K) - (binaryPrefix x m : K)) := by
  rw [globalBinaryReductionCoefficient, thueMorseBit]
  push_cast
  rw [neg_one_pow_eq_pow_mod_two]

/-- The literal q-binomial summand is pointwise equal to the q-independent
analytic binary-reduction summand. -/
theorem qBinomialFabiusGlobalSummand_eq
    (K : Type*) [RCLike K] (q : K) (x : ℝ) (m : ℕ) :
    qBinomialFabiusGlobalSummand K q x m =
      (globalBinaryReductionSummand x m : K) := by
  have hscaleK := congrArg (fun z : ℝ => (z : K))
    (two_pow_succ_mul_binaryTail x m)
  push_cast at hscaleK
  have hbase :
      (((2 : ℝ) ^ (m + 1) * x -
          2 * (binaryPrefix x m : ℝ) : ℝ) : K) =
        (2 : K) ^ (m + 1) * (binaryTail x m : K) := by
    push_cast
    exact hscaleK.symm
  rw [qBinomialFabiusGlobalSummand, globalBinaryReductionSummand]
  rw [← globalBinaryReductionCoefficient_cast K x m]
  rw [hbase]
  rw [← qBinomialFabiusReductionPolynomial_eq_sum q m (binaryTail x m : K)]
  rw [qBinomialFabiusReductionPolynomial_rclike_eq_fabiusReductionSum]
  push_cast
  rfl

/-- The literal summand is independent of the real or complex translation,
pointwise before summation. -/
theorem qBinomialFabiusGlobalSummand_independent
    (K : Type*) [RCLike K] (q₁ q₂ : K) (x : ℝ) (m : ℕ) :
    qBinomialFabiusGlobalSummand K q₁ x m =
      qBinomialFabiusGlobalSummand K q₂ x m := by
  rw [qBinomialFabiusGlobalSummand_eq,
    qBinomialFabiusGlobalSummand_eq]

/-- The norms of the literal summands are summable for every nonnegative real
input and every real or complex translation. -/
theorem summable_norm_qBinomialFabiusGlobalSummand
    (K : Type*) [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun m : ℕ => ‖qBinomialFabiusGlobalSummand K q x m‖) := by
  exact (summable_norm_globalBinaryReductionSummand F hF x hx).congr
    (fun m => by rw [qBinomialFabiusGlobalSummand_eq]; simp)

/-- The literal formula is absolutely summable for every nonnegative real
input and every real or complex translation. -/
theorem summable_qBinomialFabiusGlobalSummand
    (K : Type*) [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (x : ℝ) (hx : 0 ≤ x) :
    Summable (qBinomialFabiusGlobalSummand K q x) :=
  Summable.of_norm
    (summable_norm_qBinomialFabiusGlobalSummand K F hF q x hx)

/-- `HasSum` form of the source-literal identity, simultaneously over `ℝ`
and `ℂ`. -/
theorem hasSum_qBinomialFabiusGlobalSummand
    (K : Type*) [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (x : ℝ) (hx : 0 ≤ x) :
    HasSum (qBinomialFabiusGlobalSummand K q x)
      (extendedFabius F x : K) := by
  exact ((RCLike.hasSum_ofReal K).2
    (hasSum_globalBinaryReductionSummand F hF x hx)).congr_fun
      (fun m => qBinomialFabiusGlobalSummand_eq K q x m)

/-- `tsum` form of the source-literal identity. -/
theorem extendedFabius_eq_tsum_qBinomialFabiusGlobalSummand
    (K : Type*) [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (x : ℝ) (hx : 0 ≤ x) :
    (extendedFabius F x : K) =
      ∑' m : ℕ, qBinomialFabiusGlobalSummand K q x m :=
  (hasSum_qBinomialFabiusGlobalSummand K F hF q x hx).tsum_eq.symm

/-- Canonical signed-global formula for every real translation. -/
theorem globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_real
    (q x : ℝ) (hx : 0 ≤ x) :
    globalFabius x =
      ∑' m : ℕ, qBinomialFabiusGlobalSummand ℝ q x m := by
  rw [globalFabius,
    extendedFabius_eq_tsum_globalBinaryReductionSummand fabius fabius_spec x hx]
  apply tsum_congr
  intro m
  exact (qBinomialFabiusGlobalSummand_eq ℝ q x m).symm

/-- Canonical signed-global formula for every complex translation. -/
theorem globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_complex
    (q : ℂ) (x : ℝ) (hx : 0 ≤ x) :
    (globalFabius x : ℂ) =
      ∑' m : ℕ, qBinomialFabiusGlobalSummand ℂ q x m := by
  rw [globalFabius]
  exact extendedFabius_eq_tsum_qBinomialFabiusGlobalSummand
    ℂ fabius fabius_spec q x hx

/-- The complex theorem with every finite sum displayed.  This is the direct
Lean counterpart of the corrected Wolfram Language statement. -/
theorem globalFabius_eq_qBinomialThueMorse_global_sum_complex
    (q : ℂ) (x : ℝ) (hx : 0 ≤ x) :
    (globalFabius x : ℂ) =
      ∑' m : ℕ,
        (-1 : ℂ) ^ thueMorseBit (binaryPrefix x m) *
          (2 * (binaryPreviousPrefix x m : ℂ) - (binaryPrefix x m : ℂ)) *
          ((∑ n ∈ Finset.range (m + 1),
              (((((2 : ℝ) ^ (m + 1) * x -
                      2 * (binaryPrefix x m : ℝ) : ℝ) : ℂ) ^ (m - n) /
                  ((m - n).factorial : ℂ)) *
                ((∑ k ∈ Finset.range (n + 1),
                    algebraMap ℚ ℂ
                      (qBinomial n k (1 / 2) /
                        ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
                      ∑ r ∈ Finset.range (2 ^ k),
                        (-1 : ℂ) ^ thueMorseBit r *
                          ((r : ℂ) - (2 : ℂ) ^ k + q) ^ (n + k)) /
                  algebraMap ℚ ℂ
                    ((2 : ℚ) ^ n.choose 2 *
                      qPochhammer (1 / 2) (1 / 2) n)))) /
            (2 : ℂ) ^ (m + 1).choose 2) := by
  change (globalFabius x : ℂ) =
    ∑' m : ℕ, qBinomialFabiusGlobalSummand ℂ q x m
  exact globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_complex q x hx

/-- The rational-shift statement requested originally, regarded as a real
identity. -/
theorem globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_rat
    (q : ℚ) (x : ℝ) (hx : 0 ≤ x) :
    globalFabius x =
      ∑' m : ℕ, qBinomialFabiusGlobalSummand ℝ (q : ℝ) x m :=
  globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_real (q : ℝ) x hx

/-- On the closed unit interval the same series equals the bounded Fabius
function. -/
theorem fabiusReal_eq_tsum_qBinomialFabiusGlobalSummand
    (K : Type*) [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (fabiusReal F x : K) =
      ∑' m : ℕ, qBinomialFabiusGlobalSummand K q x m := by
  rw [← extendedFabius_eq_fabiusReal F hF hx]
  exact extendedFabius_eq_tsum_qBinomialFabiusGlobalSummand
    K F hF q x hx.1

/-- The scale-zero q-binomial polynomial is exactly one.  This includes the
endpoint convention `0 ^ 0 = 1`. -/
@[simp] theorem qBinomialFabiusGlobalSummand_zero_polynomial
    (K : Type*) [RCLike K] (q : K) (x : ℝ) :
    qBinomialFabiusReductionPolynomial q 0 (binaryTail x 0 : K) = 1 := by
  simp

/-- At `x = 1`, the restored scale-zero term contributes the missing one. -/
@[simp] theorem qBinomialFabiusGlobalSummand_one_zero
    (K : Type*) [RCLike K] (q : K) :
    qBinomialFabiusGlobalSummand K q 1 0 = 1 := by
  rw [qBinomialFabiusGlobalSummand_eq]
  norm_num [globalBinaryReductionSummand, globalBinaryReductionCoefficient,
    binaryPrefix, binaryPreviousPrefix, binaryTail, fabiusReductionSum,
    binaryWeight, halfMoment]

end

end Fabius
