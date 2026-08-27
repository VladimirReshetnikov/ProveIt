import FabiusFunction.FabiusRecurrenceSequence
import FabiusFunction.GlobalDyadic
import FabiusFunction.HalfQBinomial
import FabiusFunction.ThueMorseExponential

/-!
# A q-binomial--Thue--Morse formula for dyadic Fabius values

This module first proves the inverse-power (`m = 1`) q-binomial formula and
then its full arbitrary-numerator form.  The source formula has inner sum

`Sum[(-1)^ThueMorse[r] (r-m 2^k+1/2)^(n+k), {r,0,m 2^k-1}]`.

It equals the signed global Fabius extension at `m/2^n` for every natural
`m,n`, including zero.  On the unit interval (`m ≤ 2^n`) it also equals the
bounded Fabius function.  All subtractions are performed in `ℚ`, as in
Wolfram Language.

The proof is stronger: translating every inner power by the same `c : ℚ`
leaves the complete q-binomial numerator unchanged.  Thus the source's
mandatory `c = 1/2` expression and the centered/unshifted `c = 0` expression
have the same value.  At arbitrary dyadic arguments, the resulting finite
formula depends only on the represented rational number: numerator and
denominator exponent may be refined, and even the common translation may be
changed simultaneously.  The degenerate grids are explicit as well: zero
numerator always gives zero, while at denominator exponent zero the formula
is the Thue--Morse-signed indicator of the odd integers.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- The outer finite sum in the q-binomial--Thue--Morse formula. -/
noncomputable def qBinomialThueMorseNumerator (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    qBinomial n k (1 / 2) /
        ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
      thueMorseCenteredPowerSum k (n + k)

/-- The literal rational right-hand side of the requested Wolfram Language
formula. -/
noncomputable def qBinomialThueMorseFormula (n : ℕ) : ℚ :=
  (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    qBinomialThueMorseNumerator n

private noncomputable def recurrenceSeries : PowerSeries ℚ :=
  PowerSeries.mk fabiusRecurrenceSequence

/-- The recurrence defining the exact dyadic Fabius coefficients is the
formal-series refinement equation. -/
private theorem recurrenceSeries_rescale_two :
    PowerSeries.rescale 2 recurrenceSeries =
      rationalExpm1DivSeries * recurrenceSeries := by
  rw [mul_comm]
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul]
  simp only [recurrenceSeries, rationalExpm1DivSeries,
    PowerSeries.coeff_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [fabiusRecurrenceSequence]
  have hleft :
      (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n * halfMoment n) /
          ((n + 1).factorial : ℚ) =
        2 ^ n * (halfMoment n / (n.factorial : ℚ)) := by
    rw [Nat.factorial_succ]
    field_simp
    push_cast
    ring
  have hterm (x : ℕ) (hx : x ∈ range (n + 1)) :
      ((Nat.choose (n + 1) x : ℚ) * halfMoment x) /
          ((n + 1).factorial : ℚ) =
        halfMoment x / (x.factorial : ℚ) *
          (1 / ((n - x + 1).factorial : ℚ)) := by
    have hxlt := mem_range.1 hx
    have hxle : x ≤ n + 1 := by omega
    rw [Nat.cast_choose ℚ hxle]
    have hsub : n + 1 - x = n - x + 1 := by omega
    rw [hsub]
    field_simp
  have h := congrArg
    (fun q : ℚ => q / ((n + 1).factorial : ℚ))
    (halfMoment_original_recurrence n)
  rw [hleft] at h
  rw [Finset.sum_div] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro x hx
  exact hterm x hx

private noncomputable def negativeExpSeries : PowerSeries ℚ :=
  PowerSeries.rescale (-1) (PowerSeries.exp ℚ)

private noncomputable def refinementFactorSeries (k : ℕ) : PowerSeries ℚ :=
  negativeExpSeries * ∏ j ∈ Finset.range k,
    PowerSeries.rescale (-((2 : ℚ) ^ j)) rationalExpm1DivSeries

private theorem refinementFactorSeries_mul (k : ℕ) :
    refinementFactorSeries k * PowerSeries.rescale (-1) recurrenceSeries =
      negativeExpSeries *
        PowerSeries.rescale (-((2 : ℚ) ^ k)) recurrenceSeries := by
  rw [refinementFactorSeries, mul_assoc,
    prod_rescale_neg_expm1_mul_rescale_neg_one recurrenceSeries
      recurrenceSeries_rescale_two k]

private theorem coefficient_isolation
    (P : PowerSeries ℚ) (x : ℚ)
    (hP : P * PowerSeries.rescale (-1) recurrenceSeries =
      negativeExpSeries * PowerSeries.rescale x recurrenceSeries) (n : ℕ) :
    PowerSeries.coeff n P =
      PowerSeries.coeff n
          (negativeExpSeries * PowerSeries.rescale x recurrenceSeries) -
        ∑ i ∈ Finset.range n,
          PowerSeries.coeff i P *
            (-1 : ℚ) ^ (n - i) * fabiusRecurrenceSequence (n - i) := by
  have h := congrArg (PowerSeries.coeff n) hP
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_rescale, recurrenceSeries, PowerSeries.coeff_mk] at h
  rw [Finset.sum_range_succ] at h
  simp only [Nat.sub_self, pow_zero, fabiusRecurrenceSequence_zero,
    mul_one] at h
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_rescale, recurrenceSeries, PowerSeries.coeff_mk]
  simp only [mul_assoc] at h ⊢
  linear_combination h

private theorem coeff_negativeExpSeries (n : ℕ) :
    PowerSeries.coeff n negativeExpSeries =
      (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
  simp [negativeExpSeries, PowerSeries.coeff_exp, div_eq_mul_inv]

private theorem weighted_rescaled_product_coefficient
    {κ : Type*} [DecidableEq κ] (s : Finset κ)
    (weight node : κ → ℚ) (n : ℕ)
    (hann : ∀ d < n, ∑ k ∈ s, weight k * node k ^ d = 0) :
    (∑ k ∈ s, weight k * PowerSeries.coeff n
      (negativeExpSeries * PowerSeries.rescale (node k) recurrenceSeries)) =
        (∑ k ∈ s, weight k * node k ^ n) *
          fabiusRecurrenceSequence n := by
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_rescale, recurrenceSeries, PowerSeries.coeff_mk]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hfactor (i : ℕ) :
      (∑ k ∈ s, weight k *
          (PowerSeries.coeff i negativeExpSeries *
            (node k ^ (n - i) * fabiusRecurrenceSequence (n - i)))) =
        (PowerSeries.coeff i negativeExpSeries *
          fabiusRecurrenceSequence (n - i)) *
            ∑ k ∈ s, weight k * node k ^ (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [Finset.sum_eq_single 0]
  · rw [hfactor 0]
    simp [coeff_negativeExpSeries]
    ring
  · intro i hi hi0
    rw [hfactor i]
    have hile : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hdeg : n - i < n := Nat.sub_lt (by omega) (by omega)
    rw [hann (n - i) hdeg]
    simp
  · simp

private theorem weighted_factor_coefficient
    {κ : Type*} [DecidableEq κ] (s : Finset κ)
    (weight node : κ → ℚ) (P : κ → PowerSeries ℚ)
    (hP : ∀ k ∈ s,
      P k * PowerSeries.rescale (-1) recurrenceSeries =
        negativeExpSeries * PowerSeries.rescale (node k) recurrenceSeries)
    (n : ℕ)
    (hann : ∀ d < n, ∑ k ∈ s, weight k * node k ^ d = 0) :
    (∑ k ∈ s, weight k * PowerSeries.coeff n (P k)) =
      (∑ k ∈ s, weight k * node k ^ n) *
        fabiusRecurrenceSequence n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hisolate : ∀ k ∈ s,
          PowerSeries.coeff n (P k) =
            PowerSeries.coeff n
                (negativeExpSeries *
                  PowerSeries.rescale (node k) recurrenceSeries) -
              ∑ i ∈ Finset.range n,
                PowerSeries.coeff i (P k) * (-1 : ℚ) ^ (n - i) *
                  fabiusRecurrenceSequence (n - i) := by
        intro k hk
        exact coefficient_isolation (P k) (node k) (hP k hk) n
      calc
        (∑ k ∈ s, weight k * PowerSeries.coeff n (P k)) =
            ∑ k ∈ s, weight k *
              (PowerSeries.coeff n
                  (negativeExpSeries *
                    PowerSeries.rescale (node k) recurrenceSeries) -
                ∑ i ∈ Finset.range n,
                  PowerSeries.coeff i (P k) * (-1 : ℚ) ^ (n - i) *
                    fabiusRecurrenceSequence (n - i)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hisolate k hk]
        _ = (∑ k ∈ s, weight k * PowerSeries.coeff n
              (negativeExpSeries *
                PowerSeries.rescale (node k) recurrenceSeries)) -
            ∑ k ∈ s, weight k *
              ∑ i ∈ Finset.range n,
                PowerSeries.coeff i (P k) * (-1 : ℚ) ^ (n - i) *
                  fabiusRecurrenceSequence (n - i) := by
              simp only [mul_sub, Finset.sum_sub_distrib]
        _ = _ := by
          rw [weighted_rescaled_product_coefficient s weight node n hann]
          have hlower :
              (∑ k ∈ s, weight k *
                ∑ i ∈ Finset.range n,
                  PowerSeries.coeff i (P k) * (-1 : ℚ) ^ (n - i) *
                    fabiusRecurrenceSequence (n - i)) = 0 := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_eq_zero
            intro i hi
            have hin : i < n := Finset.mem_range.mp hi
            have hanni :
                ∀ d < i, ∑ k ∈ s, weight k * node k ^ d = 0 := by
              intro d hd
              exact hann d (hd.trans hin)
            have hiw := ih i hin hanni
            have hzero :
                ∑ k ∈ s, weight k * PowerSeries.coeff i (P k) = 0 := by
              rw [hiw, hann i hin, zero_mul]
            calc
              (∑ k ∈ s,
                weight k *
                  (PowerSeries.coeff i (P k) * (-1) ^ (n - i) *
                    fabiusRecurrenceSequence (n - i))) =
                  (∑ k ∈ s, weight k * PowerSeries.coeff i (P k)) *
                    ((-1 : ℚ) ^ (n - i) *
                      fabiusRecurrenceSequence (n - i)) := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro k _hk
                    ring
              _ = 0 := by rw [hzero, zero_mul]
          rw [hlower, sub_zero]

private noncomputable def qWeight (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 * halfQBinomial n k

private def dyadicNode (k : ℕ) : ℚ := -((2 : ℚ) ^ k)

private theorem qWeight_mul_dyadicNode_pow (n d k : ℕ) :
    qWeight n k * dyadicNode k ^ d =
      (-1 : ℚ) ^ d *
        ((-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 *
          halfQBinomial n k * ((2 : ℚ) ^ d) ^ k) := by
  have hp : (((2 : ℚ) ^ k) ^ d) = ((2 : ℚ) ^ d) ^ k := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  unfold qWeight dyadicNode
  rw [neg_pow ((2 : ℚ) ^ k) d, hp]
  ring

private theorem qWeight_nodes_zero {n d : ℕ} (hd : d < n) :
    (∑ k ∈ Finset.range (n + 1),
      qWeight n k * dyadicNode k ^ d) = 0 := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        qWeight n k * dyadicNode k ^ d) =
        (-1 : ℚ) ^ d *
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 *
              halfQBinomial n k * ((2 : ℚ) ^ d) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      exact qWeight_mul_dyadicNode_pow n d k
    _ = 0 := by rw [halfQBinomial_two_pow_sum_eq_zero hd, mul_zero]

private theorem qWeight_nodes_self (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      qWeight n k * dyadicNode k ^ n) =
        (2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        qWeight n k * dyadicNode k ^ n) =
        (-1 : ℚ) ^ n *
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 *
              halfQBinomial n k * ((2 : ℚ) ^ n) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      exact qWeight_mul_dyadicNode_pow n n k
    _ = (2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n := by
      rw [halfQBinomial_two_pow_sum_eq_self]
      have hsign : (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      calc
        (-1 : ℚ) ^ n *
              ((-1 : ℚ) ^ n * 2 ^ (n + 1).choose 2 * halfQPochhammer n) =
            (((-1 : ℚ) ^ n * (-1 : ℚ) ^ n) *
              2 ^ (n + 1).choose 2) * halfQPochhammer n := by ring
        _ = _ := by rw [hsign, one_mul]

private theorem weighted_refinementFactorSeries (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      qWeight n k * PowerSeries.coeff n (refinementFactorSeries k)) =
      ((2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n) *
        fabiusRecurrenceSequence n := by
  rw [weighted_factor_coefficient (s := Finset.range (n + 1))
    (weight := qWeight n) (node := dyadicNode) (P := refinementFactorSeries)
    (hP := fun k _hk => refinementFactorSeries_mul k) n
    (fun d hd => qWeight_nodes_zero hd)]
  rw [qWeight_nodes_self]

private theorem shiftedSeries_eq_scalar_mul (k : ℕ) :
    thueMorseShiftedPowerSeries k =
      PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
        refinementFactorSeries k := by
  simpa [refinementFactorSeries, negativeExpSeries] using
    thueMorseShiftedPowerSeries_eq_expm1_product k

private theorem coeff_shiftedSeries (k n : ℕ) :
    PowerSeries.coeff n (thueMorseShiftedPowerSeries k) =
      (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
        PowerSeries.coeff n (refinementFactorSeries k) := by
  rw [shiftedSeries_eq_scalar_mul, PowerSeries.coeff_C_mul]

private theorem four_pow_choose_mul (k : ℕ) :
    (4 : ℚ) ^ k.choose 2 =
      (2 : ℚ) ^ k.choose 2 * (2 : ℚ) ^ k.choose 2 := by
  rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]

private theorem qBinomialThueMorseNumerator_eq_weighted (n : ℕ) :
    qBinomialThueMorseNumerator n =
      ∑ k ∈ Finset.range (n + 1),
        qWeight n k * PowerSeries.coeff n (refinementFactorSeries k) := by
  rw [qBinomialThueMorseNumerator]
  simp only [qBinomial_half_eq]
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    halfQBinomial n k /
          ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
        thueMorseCenteredPowerSum k (n + k) =
        halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
          (thueMorseCenteredPowerSum k (n + k) /
            ((n + k).factorial : ℚ)) := by field_simp
    _ = halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
          PowerSeries.coeff n (thueMorseShiftedPowerSeries k) := by
      rw [coeff_thueMorseShiftedPowerSeries]
    _ = _ := by
      rw [coeff_shiftedSeries]
      unfold qWeight
      rw [four_pow_choose_mul, div_pow]
      norm_num
      field_simp

/-- The requested right-hand side reduces to the established recurrence
normalization for every natural `n`, including zero. -/
theorem qBinomialThueMorseFormula_eq_recurrenceSequence (n : ℕ) :
    qBinomialThueMorseFormula n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ * fabiusRecurrenceSequence n := by
  rw [qBinomialThueMorseFormula, qPochhammer_half_eq]
  simp only [pow_two]
  rw [qBinomialThueMorseNumerator_eq_weighted,
    weighted_refinementFactorSeries, choose_square_split, pow_add]
  have hp := halfQPochhammer_ne_zero n
  field_simp

/-- Exact rational form of the q-binomial--Thue--Morse formula for
`FabiusF[2^(-n)]`. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula (n : ℕ) :
    fabiusAtInverseTwoPow n = qBinomialThueMorseFormula n := by
  rw [qBinomialThueMorseFormula_eq_recurrenceSequence,
    fabiusAtInverseTwoPow_eq_halfMoment,
    halfMomentFabiusValue_eq_fabiusRecurrenceSequence]

/-- The rational theorem with both finite sums displayed literally.  This is
the direct Lean transcription of the requested Wolfram Language statement. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorse_sum (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (thueMorseSign r : ℚ) *
                ((r : ℚ) - (2 : ℚ) ^ k) ^ (n + k) := by
  rw [fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula]
  simp only [qBinomialThueMorseFormula, qBinomialThueMorseNumerator,
    thueMorseCenteredPowerSum_eq_sum_range]

/-- Real-valued form for any bounded function satisfying the Fabius
characterization. -/
theorem fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      (qBinomialThueMorseFormula n : ℝ) := by
  rw [fabius_inverse_two_pow_eq_recurrenceSequence F hF n,
    qBinomialThueMorseFormula_eq_recurrenceSequence]
  push_cast
  rfl

/-- The requested real-valued identity for the canonical Fabius function. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseFormula (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (qBinomialThueMorseFormula n : ℝ) :=
  fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula
    fabius fabius_spec n

/-! ## Rational translations of the inner sums -/

/-- The outer numerator after translating every centered Thue--Morse block
by the same rational constant `c`. -/
noncomputable def qBinomialThueMorseTranslatedNumerator
    (c : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    qBinomial n k (1 / 2) /
        ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
      thueMorseTranslatedPowerSum c k (n + k)

/-- The q-binomial--Thue--Morse expression with a common rational
translation `c` in every inner power sum. -/
noncomputable def qBinomialThueMorseTranslatedFormula
    (c : ℚ) (n : ℕ) : ℚ :=
  (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    qBinomialThueMorseTranslatedNumerator c n

private theorem rawWeight_mul_coeff_shifted_eq
    (n k d : ℕ) :
    halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
        PowerSeries.coeff d (thueMorseShiftedPowerSeries k) =
      qWeight n k * PowerSeries.coeff d (refinementFactorSeries k) := by
  rw [coeff_shiftedSeries]
  unfold qWeight
  rw [four_pow_choose_mul, div_pow]
  norm_num
  field_simp

private theorem weighted_shifted_coeff_eq_zero
    {n d : ℕ} (hd : d < n) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
        PowerSeries.coeff d (thueMorseShiftedPowerSeries k)) = 0 := by
  simp_rw [rawWeight_mul_coeff_shifted_eq]
  rw [weighted_factor_coefficient (s := Finset.range (n + 1))
    (weight := qWeight n) (node := dyadicNode) (P := refinementFactorSeries)
    (hP := fun k _hk => refinementFactorSeries_mul k) d
    (fun e he => qWeight_nodes_zero (he.trans hd))]
  rw [qWeight_nodes_zero hd, zero_mul]

/-- Translating all centered Thue--Morse blocks by the same rational number
does not change the q-binomial outer numerator. -/
theorem qBinomialThueMorseTranslatedNumerator_eq_centered
    (c : ℚ) (n : ℕ) :
    qBinomialThueMorseTranslatedNumerator c n =
      qBinomialThueMorseNumerator n := by
  rw [qBinomialThueMorseTranslatedNumerator,
    qBinomialThueMorseNumerator]
  simp only [qBinomial_half_eq]
  calc
    (∑ k ∈ Finset.range (n + 1),
        halfQBinomial n k /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
          thueMorseTranslatedPowerSum c k (n + k)) =
        ∑ k ∈ Finset.range (n + 1),
          halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
            PowerSeries.coeff n
              (thueMorseTranslatedShiftedPowerSeries c k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [coeff_thueMorseTranslatedShiftedPowerSeries]
      field_simp
    _ = ∑ k ∈ Finset.range (n + 1),
          halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
            PowerSeries.coeff n
              (PowerSeries.rescale c (PowerSeries.exp ℚ) *
                thueMorseShiftedPowerSeries k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [thueMorseTranslatedShiftedPowerSeries_eq_exp_mul]
    _ = ∑ k ∈ Finset.range (n + 1),
          halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
            PowerSeries.coeff n (thueMorseShiftedPowerSeries k) := by
      simp only [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_eq_single 0]
      · simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      · intro d hd hd0
        have hdle : d ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
        have hnpos : 0 < n :=
          (Nat.pos_of_ne_zero hd0).trans_le hdle
        have hdlt : n - d < n :=
          Nat.sub_lt hnpos (Nat.pos_of_ne_zero hd0)
        calc
          (∑ k ∈ Finset.range (n + 1),
              halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
                (PowerSeries.coeff d
                    (PowerSeries.rescale c (PowerSeries.exp ℚ)) *
                  PowerSeries.coeff (n - d)
                    (thueMorseShiftedPowerSeries k))) =
              PowerSeries.coeff d
                  (PowerSeries.rescale c (PowerSeries.exp ℚ)) *
                ∑ k ∈ Finset.range (n + 1),
                  halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
                    PowerSeries.coeff (n - d)
                      (thueMorseShiftedPowerSeries k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
          _ = 0 := by
            rw [weighted_shifted_coeff_eq_zero hdlt, mul_zero]
      · simp
    _ = ∑ k ∈ Finset.range (n + 1),
          halfQBinomial n k /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            thueMorseCenteredPowerSum k (n + k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [coeff_thueMorseShiftedPowerSeries]
      field_simp

/-- The complete rational expression is invariant under a common rational
translation of its inner sums. -/
theorem qBinomialThueMorseTranslatedFormula_eq_centered
    (c : ℚ) (n : ℕ) :
    qBinomialThueMorseTranslatedFormula c n =
      qBinomialThueMorseFormula n := by
  rw [qBinomialThueMorseTranslatedFormula,
    qBinomialThueMorseFormula,
    qBinomialThueMorseTranslatedNumerator_eq_centered]

/-- Every rationally translated version gives the same exact dyadic Fabius
value. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorseTranslatedFormula
    (c : ℚ) (n : ℕ) :
    fabiusAtInverseTwoPow n =
      qBinomialThueMorseTranslatedFormula c n := by
  rw [qBinomialThueMorseTranslatedFormula_eq_centered,
    fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula]

/-- Real-valued translated identity for every function satisfying the
Fabius characterization. -/
theorem fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormula
    (F : BoundedFabius) (hF : IsFabius F) (c : ℚ) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      (qBinomialThueMorseTranslatedFormula c n : ℝ) := by
  rw [qBinomialThueMorseTranslatedFormula_eq_centered,
    fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula F hF]

/-- The rational formula requested in the question, with translation
`c = 1/2`. -/
noncomputable def qBinomialThueMorseHalfShiftFormula (n : ℕ) : ℚ :=
  qBinomialThueMorseTranslatedFormula (1 / 2) n

/-- Exact rational half-shifted q-binomial formula. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorseHalfShiftFormula
    (n : ℕ) :
    fabiusAtInverseTwoPow n =
      qBinomialThueMorseHalfShiftFormula n :=
  fabiusAtInverseTwoPow_eq_qBinomialThueMorseTranslatedFormula (1 / 2) n

/-- The half-shifted real-valued identity for the canonical Fabius
function. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseHalfShiftFormula
    (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (qBinomialThueMorseHalfShiftFormula n : ℝ) :=
  fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormula
    fabius fabius_spec (1 / 2) n

/-- The rational half-shifted theorem with both sums displayed literally.
This is the direct Lean transcription of the requested Wolfram Language
statement, including `n = 0`. -/
theorem fabiusAtInverseTwoPow_eq_qBinomialThueMorse_halfShift_sum (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (thueMorseSign r : ℚ) *
                ((r : ℚ) - (2 : ℚ) ^ k + (1 / 2 : ℚ)) ^ (n + k) := by
  rw [fabiusAtInverseTwoPow_eq_qBinomialThueMorseHalfShiftFormula]
  simp only [qBinomialThueMorseHalfShiftFormula,
    qBinomialThueMorseTranslatedFormula,
    qBinomialThueMorseTranslatedNumerator,
    thueMorseTranslatedPowerSum_eq_sum_range]

/-! ## Arbitrary nonnegative dyadic numerators -/

/-- The centered/unshifted auxiliary Thue--Morse power sum for the dyadic
numerator `m`.  Subtraction takes place in `ℚ`, so this also covers
numerators larger than the denominator. -/
def thueMorseDyadicNumeratorPowerSum (m k d : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (m * 2 ^ k),
    (thueMorseSign r : ℚ) *
      ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k) ^ d

/-- The centered/unshifted rational q-binomial expression for an arbitrary
natural numerator `m`. -/
noncomputable def qBinomialThueMorseDyadicFormula (m n : ℕ) : ℚ :=
  (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    ∑ k ∈ Finset.range (n + 1),
      qBinomial n k (1 / 2) /
          ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
        thueMorseDyadicNumeratorPowerSum m k (n + k)

private noncomputable def dyadicNumeratorPrefixSeries (m : ℕ) :
    PowerSeries ℚ :=
  ∑ h ∈ Finset.range m, (thueMorseSign h : ℚ) •
    PowerSeries.rescale ((m : ℚ) - 1 - h) (PowerSeries.exp ℚ)

private theorem rescale_smul_rat
    (a c : ℚ) (P : PowerSeries ℚ) :
    PowerSeries.rescale a (c • P) =
      c • PowerSeries.rescale a P := by
  ext d
  simp only [PowerSeries.coeff_rescale, map_smul, smul_eq_mul]
  ring

private noncomputable def thueMorseDyadicNumeratorPowerSeries
    (m k : ℕ) : PowerSeries ℚ :=
  ∑ r ∈ Finset.range (m * 2 ^ k), (thueMorseSign r : ℚ) •
    PowerSeries.rescale
      ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k)
      (PowerSeries.exp ℚ)

private theorem coeff_thueMorseDyadicNumeratorPowerSeries
    (m k d : ℕ) :
    PowerSeries.coeff d (thueMorseDyadicNumeratorPowerSeries m k) =
      thueMorseDyadicNumeratorPowerSum m k d / d.factorial := by
  rw [thueMorseDyadicNumeratorPowerSeries,
    thueMorseDyadicNumeratorPowerSum]
  simp only [map_sum, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, map_smul, smul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _hr
  norm_num
  ring

private theorem thueMorseDyadicNumeratorPowerSeries_factor
    (m k : ℕ) :
    thueMorseDyadicNumeratorPowerSeries m k =
      PowerSeries.rescale (dyadicNode k) (dyadicNumeratorPrefixSeries m) *
        thueMorseCenteredPowerSeries k := by
  rw [thueMorseDyadicNumeratorPowerSeries,
    sum_range_block_decomposition (fun r => (thueMorseSign r : ℚ) •
      PowerSeries.rescale
        ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k)
        (PowerSeries.exp ℚ)) m (2 ^ k)]
  rw [dyadicNumeratorPrefixSeries, map_sum]
  rw [thueMorseCenteredPowerSeries,
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ => (thueMorseSign r : ℚ) •
        PowerSeries.rescale ((r : ℚ) - (2 : ℚ) ^ k)
          (PowerSeries.exp ℚ)) (2 ^ k)]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < 2 ^ k := Finset.mem_range.mp hr
  rw [thueMorseSign_block_concat k h r hrlt]
  push_cast
  rw [rescale_smul_rat, PowerSeries.rescale_rescale,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    PowerSeries.exp_mul_exp_eq_exp_add]
  congr 2
  unfold dyadicNode
  ring_nf

private noncomputable def dyadicNumeratorRefinementFactorSeries
    (m k : ℕ) : PowerSeries ℚ :=
  PowerSeries.rescale (dyadicNode k) (dyadicNumeratorPrefixSeries m) *
    refinementFactorSeries k

private theorem coeff_dyadicNumeratorRefinementFactorSeries
    (m k n : ℕ) :
    thueMorseDyadicNumeratorPowerSum m k (n + k) /
        ((n + k).factorial : ℚ) =
      (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
        PowerSeries.coeff n
          (dyadicNumeratorRefinementFactorSeries m k) := by
  have hfull := thueMorseDyadicNumeratorPowerSeries_factor m k
  have hshift :
      PowerSeries.X ^ k *
          (PowerSeries.rescale (dyadicNode k)
              (dyadicNumeratorPrefixSeries m) *
            thueMorseShiftedPowerSeries k) =
        thueMorseDyadicNumeratorPowerSeries m k := by
    rw [hfull, ← X_pow_mul_thueMorseShiftedPowerSeries k]
    ring
  have hc := congrArg (PowerSeries.coeff (n + k)) hshift
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_right,
    coeff_thueMorseDyadicNumeratorPowerSeries] at hc
  rw [shiftedSeries_eq_scalar_mul] at hc
  rw [show
      PowerSeries.rescale (dyadicNode k) (dyadicNumeratorPrefixSeries m) *
          (PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
            refinementFactorSeries k) =
        PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
          dyadicNumeratorRefinementFactorSeries m k by
      rw [dyadicNumeratorRefinementFactorSeries]
      ring,
    PowerSeries.coeff_C_mul] at hc
  exact hc.symm

private theorem weighted_dyadicNumeratorRefinementFactorSeries_degree
    (m n d : ℕ) (hd : d ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      qWeight n k * PowerSeries.coeff d
        (dyadicNumeratorRefinementFactorSeries m k)) =
      (∑ k ∈ Finset.range (n + 1),
        qWeight n k * dyadicNode k ^ d) *
        PowerSeries.coeff d
          (dyadicNumeratorPrefixSeries m * recurrenceSeries) := by
  simp only [dyadicNumeratorRefinementFactorSeries,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_rescale]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [recurrenceSeries, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hile : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hann (e : ℕ) (he : e < d - i) :
      (∑ k ∈ Finset.range (n + 1),
        (qWeight n k * dyadicNode k ^ i) * dyadicNode k ^ e) = 0 := by
    have hie : i + e < n := by omega
    rw [show (∑ k ∈ Finset.range (n + 1),
        (qWeight n k * dyadicNode k ^ i) * dyadicNode k ^ e) =
      ∑ k ∈ Finset.range (n + 1),
        qWeight n k * dyadicNode k ^ (i + e) by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [pow_add]
      ring]
    exact qWeight_nodes_zero hie
  have hweighted := weighted_factor_coefficient
    (s := Finset.range (n + 1))
    (weight := fun k => qWeight n k * dyadicNode k ^ i)
    (node := dyadicNode) (P := refinementFactorSeries)
    (hP := fun k _hk => refinementFactorSeries_mul k)
    (d - i) hann
  have hnode :
      (∑ k ∈ Finset.range (n + 1),
        (qWeight n k * dyadicNode k ^ i) *
          dyadicNode k ^ (d - i)) =
      ∑ k ∈ Finset.range (n + 1),
        qWeight n k * dyadicNode k ^ d := by
    apply Finset.sum_congr rfl
    intro k _hk
    calc
      qWeight n k * dyadicNode k ^ i * dyadicNode k ^ (d - i) =
          qWeight n k *
            (dyadicNode k ^ i * dyadicNode k ^ (d - i)) := by ring
      _ = qWeight n k * dyadicNode k ^ d := by
        rw [← pow_add, Nat.add_sub_of_le hile]
  rw [hnode] at hweighted
  calc
    (∑ k ∈ Finset.range (n + 1),
        qWeight n k *
          (dyadicNode k ^ i *
            PowerSeries.coeff i (dyadicNumeratorPrefixSeries m) *
              PowerSeries.coeff (d - i) (refinementFactorSeries k))) =
      PowerSeries.coeff i (dyadicNumeratorPrefixSeries m) *
        ∑ k ∈ Finset.range (n + 1),
          (qWeight n k * dyadicNode k ^ i) *
            PowerSeries.coeff (d - i) (refinementFactorSeries k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
    _ = PowerSeries.coeff i (dyadicNumeratorPrefixSeries m) *
        ((∑ k ∈ Finset.range (n + 1),
          qWeight n k * dyadicNode k ^ d) *
          fabiusRecurrenceSequence (d - i)) := by rw [hweighted]
    _ = (∑ k ∈ Finset.range (n + 1),
        qWeight n k * dyadicNode k ^ d) *
        (PowerSeries.coeff i (dyadicNumeratorPrefixSeries m) *
          fabiusRecurrenceSequence (d - i)) := by ring

private theorem weighted_dyadicNumeratorRefinementFactorSeries (m n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      qWeight n k * PowerSeries.coeff n
        (dyadicNumeratorRefinementFactorSeries m k)) =
      ((2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n) *
        PowerSeries.coeff n
          (dyadicNumeratorPrefixSeries m * recurrenceSeries) := by
  rw [weighted_dyadicNumeratorRefinementFactorSeries_degree m n n le_rfl,
    qWeight_nodes_self]

private theorem qBinomialThueMorseDyadicNumerator_eq_weighted (m n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      qBinomial n k (1 / 2) /
          ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
        thueMorseDyadicNumeratorPowerSum m k (n + k)) =
      ∑ k ∈ Finset.range (n + 1),
        qWeight n k * PowerSeries.coeff n
          (dyadicNumeratorRefinementFactorSeries m k) := by
  simp only [qBinomial_half_eq]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [show
      halfQBinomial n k /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
          thueMorseDyadicNumeratorPowerSum m k (n + k) =
        halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
          (thueMorseDyadicNumeratorPowerSum m k (n + k) /
            ((n + k).factorial : ℚ)) by field_simp,
    coeff_dyadicNumeratorRefinementFactorSeries]
  unfold qWeight
  rw [four_pow_choose_mul, div_pow]
  norm_num
  field_simp

/-- The arbitrary-numerator q-binomial expression is the coefficient of its
finite Thue--Morse prefix series, with the same dyadic normalization as in
the inverse-power formula. -/
theorem qBinomialThueMorseDyadicFormula_eq_prefixCoefficient (m n : ℕ) :
    qBinomialThueMorseDyadicFormula m n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ *
        PowerSeries.coeff n (dyadicNumeratorPrefixSeries m * recurrenceSeries) := by
  rw [qBinomialThueMorseDyadicFormula, qPochhammer_half_eq,
    qBinomialThueMorseDyadicNumerator_eq_weighted,
    weighted_dyadicNumeratorRefinementFactorSeries]
  simp only [pow_two]
  rw [
    choose_square_split, pow_add]
  have hp := halfQPochhammer_ne_zero n
  field_simp

private theorem recurrenceSeries_eq_expHalf_mul_centeredMomentPowerSeries :
    recurrenceSeries =
      PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) *
        centeredMomentPowerSeries := by
  ext n
  rw [coeff_expHalf_mul_centeredMomentPowerSeries]
  simp only [recurrenceSeries, PowerSeries.coeff_mk,
    fabiusRecurrenceSequence, halfMoment_eq_evenMomentSum]
  field_simp

private theorem fabiusDyadic_eq_range_sum (n m : ℕ) :
    fabiusDyadic n m =
      (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial *
        ∑ h ∈ Finset.range m, (thueMorseSign h : ℚ) *
          ∑ k ∈ Finset.range (n / 2 + 1),
            (Nat.choose n (2 * k) : ℚ) *
              ((2 : ℚ) * m - 2 * h - 1) ^ (n - 2 * k) * moment k := by
  rw [fabiusDyadic,
    Fin.sum_univ_eq_sum_range
      (fun h : ℕ => (thueMorseSign h : ℚ) *
        ∑ k : Fin (n / 2 + 1),
          (Nat.choose n (2 * k.val) : ℚ) *
            ((2 : ℚ) * m - 2 * h - 1) ^ (n - 2 * k.val) *
              moment k.val) m]
  congr 1
  apply Finset.sum_congr rfl
  intro h _hh
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      (Nat.choose n (2 * k) : ℚ) *
        ((2 : ℚ) * m - 2 * h - 1) ^ (n - 2 * k) * moment k)
    (n / 2 + 1)]

/-- The coefficient isolated by the q-binomial weights is exactly the
closed rational dyadic Fabius value. -/
theorem coeff_dyadicNumeratorPrefixSeries_mul_recurrenceSeries
    (m n : ℕ) :
    PowerSeries.coeff n (dyadicNumeratorPrefixSeries m * recurrenceSeries) =
      (2 : ℚ) ^ n.choose 2 * fabiusDyadic n m := by
  rw [recurrenceSeries_eq_expHalf_mul_centeredMomentPowerSeries,
    dyadicNumeratorPrefixSeries, Finset.sum_mul]
  simp only [smul_mul_assoc]
  have hterm (h : ℕ) :
      PowerSeries.rescale ((m : ℚ) - 1 - h) (PowerSeries.exp ℚ) *
          (PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) *
            centeredMomentPowerSeries) =
        PowerSeries.rescale ((m : ℚ) - h - 1 / 2) (PowerSeries.exp ℚ) *
          centeredMomentPowerSeries := by
    rw [← mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
    congr 2
    ring_nf
  simp_rw [hterm]
  simp only [map_sum, map_smul, smul_eq_mul,
    coeff_exp_mul_centeredMomentPowerSeries]
  rw [fabiusDyadic_eq_range_sum]
  have hchoose : (n + 1).choose 2 = n + n.choose 2 := by
    simp [Nat.choose_succ_succ, Nat.choose_one_right]
  have hzpow :
      (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) =
        ((2 : ℚ) ^ Nat.choose (n + 1) 2)⁻¹ := by
    rw [zpow_neg]
    norm_num [zpow_natCast]
  rw [hzpow, hchoose, pow_add]
  field_simp
  rw [← Finset.sum_div]
  field_simp

/-- Exact rational arbitrary-numerator q-binomial--Thue--Morse formula. -/
theorem fabiusDyadic_eq_qBinomialThueMorseDyadicFormula (m n : ℕ) :
    fabiusDyadic n m = qBinomialThueMorseDyadicFormula m n := by
  rw [qBinomialThueMorseDyadicFormula_eq_prefixCoefficient,
    coeff_dyadicNumeratorPrefixSeries_mul_recurrenceSeries]
  field_simp

/-- At zero numerator the centered arbitrary-dyadic formula vanishes, for
every denominator exponent. -/
@[simp] theorem qBinomialThueMorseDyadicFormula_zero (n : ℕ) :
    qBinomialThueMorseDyadicFormula 0 n = 0 := by
  calc
    qBinomialThueMorseDyadicFormula 0 n = fabiusDyadic n 0 :=
      (fabiusDyadic_eq_qBinomialThueMorseDyadicFormula 0 n).symm
    _ = 0 := fabiusDyadic_arg_zero n

/-- At numerator one, the arbitrary-dyadic q-binomial formula is exactly the
inverse-dyadic formula. -/
theorem qBinomialThueMorseDyadicFormula_one (n : ℕ) :
    qBinomialThueMorseDyadicFormula 1 n =
      qBinomialThueMorseFormula n := by
  calc
    qBinomialThueMorseDyadicFormula 1 n = fabiusDyadic n 1 :=
      (fabiusDyadic_eq_qBinomialThueMorseDyadicFormula 1 n).symm
    _ = fabiusAtInverseTwoPow n := rfl
    _ = qBinomialThueMorseFormula n :=
      fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula n

private theorem weighted_dyadicNumeratorRefinementFactorSeries_eq_zero
    {m n d : ℕ} (hd : d < n) :
    (∑ k ∈ Finset.range (n + 1),
      qWeight n k * PowerSeries.coeff d
        (dyadicNumeratorRefinementFactorSeries m k)) = 0 := by
  rw [weighted_dyadicNumeratorRefinementFactorSeries_degree
      m n d (Nat.le_of_lt hd),
    qWeight_nodes_zero hd, zero_mul]

private noncomputable def dyadicNumeratorShiftedPowerSeries
    (m k : ℕ) : PowerSeries ℚ :=
  PowerSeries.rescale (dyadicNode k) (dyadicNumeratorPrefixSeries m) *
    thueMorseShiftedPowerSeries k

private theorem coeff_dyadicNumeratorShiftedPowerSeries
    (m k n : ℕ) :
    PowerSeries.coeff n (dyadicNumeratorShiftedPowerSeries m k) =
      thueMorseDyadicNumeratorPowerSum m k (n + k) /
        ((n + k).factorial : ℚ) := by
  rw [dyadicNumeratorShiftedPowerSeries, shiftedSeries_eq_scalar_mul]
  rw [show
      PowerSeries.rescale (dyadicNode k) (dyadicNumeratorPrefixSeries m) *
          (PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
            refinementFactorSeries k) =
        PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
          dyadicNumeratorRefinementFactorSeries m k by
      rw [dyadicNumeratorRefinementFactorSeries]
      ring,
    PowerSeries.coeff_C_mul,
    ← coeff_dyadicNumeratorRefinementFactorSeries]

private theorem rawWeight_mul_coeff_dyadicNumeratorShifted_eq
    (m n k d : ℕ) :
    halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
        PowerSeries.coeff d (dyadicNumeratorShiftedPowerSeries m k) =
      qWeight n k * PowerSeries.coeff d
        (dyadicNumeratorRefinementFactorSeries m k) := by
  rw [dyadicNumeratorShiftedPowerSeries, shiftedSeries_eq_scalar_mul]
  rw [show
      PowerSeries.rescale (dyadicNode k) (dyadicNumeratorPrefixSeries m) *
          (PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
            refinementFactorSeries k) =
        PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
          dyadicNumeratorRefinementFactorSeries m k by
      rw [dyadicNumeratorRefinementFactorSeries]
      ring,
    PowerSeries.coeff_C_mul]
  unfold qWeight
  rw [four_pow_choose_mul, div_pow]
  norm_num
  field_simp

private theorem weighted_dyadicNumeratorShifted_coeff_eq_zero
    {m n d : ℕ} (hd : d < n) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
        PowerSeries.coeff d (dyadicNumeratorShiftedPowerSeries m k)) = 0 := by
  simp_rw [rawWeight_mul_coeff_dyadicNumeratorShifted_eq]
  exact weighted_dyadicNumeratorRefinementFactorSeries_eq_zero hd

/-- The arbitrary-numerator inner sum after a common rational translation. -/
def thueMorseDyadicNumeratorTranslatedPowerSum
    (c : ℚ) (m k d : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (m * 2 ^ k),
    (thueMorseSign r : ℚ) *
      ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k + c) ^ d

private noncomputable def thueMorseDyadicNumeratorTranslatedPowerSeries
    (c : ℚ) (m k : ℕ) : PowerSeries ℚ :=
  ∑ r ∈ Finset.range (m * 2 ^ k), (thueMorseSign r : ℚ) •
    PowerSeries.rescale
      ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k + c)
      (PowerSeries.exp ℚ)

private theorem coeff_thueMorseDyadicNumeratorTranslatedPowerSeries
    (c : ℚ) (m k d : ℕ) :
    PowerSeries.coeff d
        (thueMorseDyadicNumeratorTranslatedPowerSeries c m k) =
      thueMorseDyadicNumeratorTranslatedPowerSum c m k d /
        d.factorial := by
  rw [thueMorseDyadicNumeratorTranslatedPowerSeries,
    thueMorseDyadicNumeratorTranslatedPowerSum]
  simp only [map_sum, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, map_smul, smul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _hr
  norm_num
  ring

private theorem thueMorseDyadicNumeratorTranslatedPowerSeries_eq_exp_mul
    (c : ℚ) (m k : ℕ) :
    thueMorseDyadicNumeratorTranslatedPowerSeries c m k =
      PowerSeries.rescale c (PowerSeries.exp ℚ) *
        thueMorseDyadicNumeratorPowerSeries m k := by
  rw [thueMorseDyadicNumeratorTranslatedPowerSeries,
    thueMorseDyadicNumeratorPowerSeries, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [mul_smul_comm, PowerSeries.exp_mul_exp_eq_exp_add]
  congr 2
  ring_nf

private theorem X_pow_mul_dyadicNumeratorShiftedPowerSeries
    (m k : ℕ) :
    PowerSeries.X ^ k * dyadicNumeratorShiftedPowerSeries m k =
      thueMorseDyadicNumeratorPowerSeries m k := by
  rw [dyadicNumeratorShiftedPowerSeries,
    thueMorseDyadicNumeratorPowerSeries_factor,
    ← X_pow_mul_thueMorseShiftedPowerSeries k]
  ring

private noncomputable def dyadicNumeratorTranslatedShiftedPowerSeries
    (c : ℚ) (m k : ℕ) : PowerSeries ℚ :=
  PowerSeries.rescale c (PowerSeries.exp ℚ) *
    dyadicNumeratorShiftedPowerSeries m k

private theorem X_pow_mul_dyadicNumeratorTranslatedShiftedPowerSeries
    (c : ℚ) (m k : ℕ) :
    PowerSeries.X ^ k *
        dyadicNumeratorTranslatedShiftedPowerSeries c m k =
      thueMorseDyadicNumeratorTranslatedPowerSeries c m k := by
  calc
    PowerSeries.X ^ k *
        dyadicNumeratorTranslatedShiftedPowerSeries c m k =
      PowerSeries.rescale c (PowerSeries.exp ℚ) *
        (PowerSeries.X ^ k * dyadicNumeratorShiftedPowerSeries m k) := by
          rw [dyadicNumeratorTranslatedShiftedPowerSeries]
          ring
    _ = PowerSeries.rescale c (PowerSeries.exp ℚ) *
        thueMorseDyadicNumeratorPowerSeries m k := by
          rw [X_pow_mul_dyadicNumeratorShiftedPowerSeries]
    _ = _ :=
      (thueMorseDyadicNumeratorTranslatedPowerSeries_eq_exp_mul c m k).symm

private theorem coeff_dyadicNumeratorTranslatedShiftedPowerSeries
    (c : ℚ) (m k n : ℕ) :
    PowerSeries.coeff n
        (dyadicNumeratorTranslatedShiftedPowerSeries c m k) =
      thueMorseDyadicNumeratorTranslatedPowerSum c m k (n + k) /
        ((n + k).factorial : ℚ) := by
  have h := congrArg (PowerSeries.coeff (n + k))
    (X_pow_mul_dyadicNumeratorTranslatedShiftedPowerSeries c m k)
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    Nat.add_sub_cancel_right,
    coeff_thueMorseDyadicNumeratorTranslatedPowerSeries] at h
  exact h

/-- The arbitrary-numerator q-binomial formula with a common rational
translation `c` in every inner power. -/
noncomputable def qBinomialThueMorseDyadicTranslatedFormula
    (c : ℚ) (m n : ℕ) : ℚ :=
  (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    ∑ k ∈ Finset.range (n + 1),
      qBinomial n k (1 / 2) /
          ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
        thueMorseDyadicNumeratorTranslatedPowerSum c m k (n + k)

private theorem qBinomialThueMorseDyadicTranslatedNumerator_eq
    (c : ℚ) (m n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      qBinomial n k (1 / 2) /
          ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
        thueMorseDyadicNumeratorTranslatedPowerSum c m k (n + k)) =
      ∑ k ∈ Finset.range (n + 1),
        qBinomial n k (1 / 2) /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
          thueMorseDyadicNumeratorPowerSum m k (n + k) := by
  simp only [qBinomial_half_eq]
  calc
    (∑ k ∈ Finset.range (n + 1),
        halfQBinomial n k /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
          thueMorseDyadicNumeratorTranslatedPowerSum c m k (n + k)) =
      ∑ k ∈ Finset.range (n + 1),
        halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
          PowerSeries.coeff n
            (dyadicNumeratorTranslatedShiftedPowerSeries c m k) := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [coeff_dyadicNumeratorTranslatedShiftedPowerSeries]
        field_simp
    _ = ∑ k ∈ Finset.range (n + 1),
        halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
          PowerSeries.coeff n (dyadicNumeratorShiftedPowerSeries m k) := by
        simp only [dyadicNumeratorTranslatedShiftedPowerSeries,
          PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm, Finset.sum_eq_single 0]
        · simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
        · intro d hd hd0
          have hdle : d ≤ n :=
            Nat.le_of_lt_succ (Finset.mem_range.mp hd)
          have hnpos : 0 < n :=
            (Nat.pos_of_ne_zero hd0).trans_le hdle
          have hdlt : n - d < n :=
            Nat.sub_lt hnpos (Nat.pos_of_ne_zero hd0)
          calc
            (∑ k ∈ Finset.range (n + 1),
                halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
                  (PowerSeries.coeff d
                      (PowerSeries.rescale c (PowerSeries.exp ℚ)) *
                    PowerSeries.coeff (n - d)
                      (dyadicNumeratorShiftedPowerSeries m k))) =
              PowerSeries.coeff d
                  (PowerSeries.rescale c (PowerSeries.exp ℚ)) *
                ∑ k ∈ Finset.range (n + 1),
                  halfQBinomial n k / (4 : ℚ) ^ k.choose 2 *
                    PowerSeries.coeff (n - d)
                      (dyadicNumeratorShiftedPowerSeries m k) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _hk
                ring
            _ = 0 := by
              rw [weighted_dyadicNumeratorShifted_coeff_eq_zero hdlt,
                mul_zero]
        · simp
    _ = ∑ k ∈ Finset.range (n + 1),
        halfQBinomial n k /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) *
          thueMorseDyadicNumeratorPowerSum m k (n + k) := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [coeff_dyadicNumeratorShiftedPowerSeries]
        field_simp

/-- A common rational translation of every inner power leaves the complete
arbitrary-numerator q-binomial formula unchanged. -/
theorem qBinomialThueMorseDyadicTranslatedFormula_eq_centered
    (c : ℚ) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormula c m n =
      qBinomialThueMorseDyadicFormula m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormula,
    qBinomialThueMorseDyadicFormula,
    qBinomialThueMorseDyadicTranslatedNumerator_eq]

/-- At zero numerator every translated arbitrary-dyadic formula vanishes,
independently of the translation and denominator exponent. -/
@[simp] theorem qBinomialThueMorseDyadicTranslatedFormula_zero
    (c : ℚ) (n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormula c 0 n = 0 := by
  rw [qBinomialThueMorseDyadicTranslatedFormula_eq_centered,
    qBinomialThueMorseDyadicFormula_zero]

/-- Exact rational arbitrary-numerator formula for every common rational
translation. -/
theorem fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    (c : ℚ) (m n : ℕ) :
    fabiusDyadic n m =
      qBinomialThueMorseDyadicTranslatedFormula c m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormula_eq_centered,
    fabiusDyadic_eq_qBinomialThueMorseDyadicFormula]

/-- At denominator exponent zero the translated formula vanishes on even
integers and, on an odd integer `m`, is the Thue--Morse sign of the binary
prefix `m / 2`.  The value is independent of the common translation. -/
@[simp] theorem qBinomialThueMorseDyadicTranslatedFormula_exponent_zero
    (c : ℚ) (m : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormula c m 0 =
      if Even m then 0 else (thueMorseSign (m / 2) : ℚ) := by
  rw [← fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula]
  apply Rat.cast_injective (α := ℝ)
  calc
    (fabiusDyadic 0 m : ℝ) =
        extendedFabius fabius ((m : ℝ) / (2 : ℝ) ^ 0) :=
      fabiusDyadic_cast_extended_nat fabius fabius_spec 0 m
    _ = extendedFabius fabius (m : ℝ) := by norm_num
    _ = if Even m then 0 else (-1 : ℝ) ^ binaryWeight (m / 2) :=
      extendedFabius_natCast_eq_ite fabius fabius_spec m
    _ = if Even m then 0 else (thueMorseSign (m / 2) : ℝ) := by
      simp [thueMorseSign]
    _ = ((if Even m then 0 else (thueMorseSign (m / 2) : ℚ) : ℚ) : ℝ) := by
      by_cases hm : Even m <;> simp [hm]

/-- The fully displayed arbitrary-rational-translation identity.  This is the
Wolfram-language formula with its common inner translation represented by
`q : ℚ`; it is valid for all natural `m,n`. -/
theorem fabiusDyadic_eq_qBinomialThueMorseDyadic_translated_sum
    (q : ℚ) (m n : ℕ) :
    fabiusDyadic n m =
      (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((2 : ℚ) ^ (k * (k - 1)) * ((n + k).factorial : ℚ)) *
            ∑ j ∈ Finset.range (m * 2 ^ k),
              (thueMorseSign j : ℚ) *
                ((j : ℚ) - (m : ℚ) * (2 : ℚ) ^ k + q) ^
                  (n + k) := by
  rw [fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula q m n]
  simp only [qBinomialThueMorseDyadicTranslatedFormula,
    thueMorseDyadicNumeratorTranslatedPowerSum, four_pow_choose_two]

/-- The source formula, with the mandatory common translation `c = 1/2`. -/
noncomputable def qBinomialThueMorseDyadicHalfShiftFormula
    (m n : ℕ) : ℚ :=
  qBinomialThueMorseDyadicTranslatedFormula (1 / 2) m n

/-- Exact rational arbitrary-numerator half-shifted formula. -/
theorem fabiusDyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula
    (m n : ℕ) :
    fabiusDyadic n m =
      qBinomialThueMorseDyadicHalfShiftFormula m n :=
  fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula (1 / 2) m n

/-- The fully displayed rational identity from the source.  It is valid for
all natural `m,n`; in particular no assumption `m ≤ 2^n` is made. -/
theorem fabiusDyadic_eq_qBinomialThueMorseDyadic_halfShift_sum
    (m n : ℕ) :
    fabiusDyadic n m =
      (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((2 : ℚ) ^ (k * (k - 1)) * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (m * 2 ^ k),
              (thueMorseSign r : ℚ) *
                ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k +
                  (1 / 2 : ℚ)) ^ (n + k) := by
  rw [fabiusDyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula]
  simp only [qBinomialThueMorseDyadicHalfShiftFormula,
    qBinomialThueMorseDyadicTranslatedFormula,
    thueMorseDyadicNumeratorTranslatedPowerSum,
    four_pow_choose_two]

/-- The fully displayed unshifted rational identity. -/
theorem fabiusDyadic_eq_qBinomialThueMorseDyadic_sum
    (m n : ℕ) :
    fabiusDyadic n m =
      (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((2 : ℚ) ^ (k * (k - 1)) * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (m * 2 ^ k),
              (thueMorseSign r : ℚ) *
                ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k) ^
                  (n + k) := by
  rw [fabiusDyadic_eq_qBinomialThueMorseDyadicFormula]
  simp only [qBinomialThueMorseDyadicFormula,
    thueMorseDyadicNumeratorPowerSum, four_pow_choose_two]

/-- Global real-valued form for every bounded function satisfying the
Fabius characterization. -/
theorem extendedFabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula
    (F : BoundedFabius) (hF : IsFabius F) (m n : ℕ) :
    extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicHalfShiftFormula m n : ℝ) := by
  calc
    extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) =
        (fabiusDyadic n m : ℝ) :=
      (fabiusDyadic_cast_extended_nat F hF n m).symm
    _ = (qBinomialThueMorseDyadicHalfShiftFormula m n : ℝ) := by
      rw [fabiusDyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula]

/-- Canonical signed-global Fabius identity at every nonnegative dyadic
argument. -/
theorem extendedFabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula_canonical
    (m n : ℕ) :
    extendedFabius fabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicHalfShiftFormula m n : ℝ) :=
  extendedFabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula
    fabius fabius_spec m n

/-- Source-facing canonical signed-global half-shifted formula. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula
    (m n : ℕ) :
    globalFabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicHalfShiftFormula m n : ℝ) := by
  rw [globalFabius]
  exact
    extendedFabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula_canonical
      m n

/-- On the unit dyadic interval, the same expression evaluates the bounded
Fabius function. -/
theorem fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula
    (F : BoundedFabius) (hF : IsFabius F) (m n : ℕ)
    (hm : m ≤ 2 ^ n) :
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicHalfShiftFormula m n : ℝ) := by
  calc
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
        (fabiusDyadic n m : ℝ) := (fabiusDyadic_cast F hF n m hm).symm
    _ = (qBinomialThueMorseDyadicHalfShiftFormula m n : ℝ) := by
      rw [fabiusDyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula]

/-- Canonical bounded-function corollary on `0 ≤ m/2^n ≤ 1`. -/
theorem fabius_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula
    (m n : ℕ) (hm : m ≤ 2 ^ n) :
    fabiusReal fabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicHalfShiftFormula m n : ℝ) :=
  fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicHalfShiftFormula
    fabius fabius_spec m n hm

/-- Global real-valued formula with an arbitrary common translation. -/
theorem extendedFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    (F : BoundedFabius) (hF : IsFabius F) (c : ℚ) (m n : ℕ) :
    extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicTranslatedFormula c m n : ℝ) := by
  calc
    extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) =
        (fabiusDyadic n m : ℝ) :=
      (fabiusDyadic_cast_extended_nat F hF n m).symm
    _ = (qBinomialThueMorseDyadicTranslatedFormula c m n : ℝ) := by
      rw [fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula]

/-- Canonical signed-global arbitrary-translation formula. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    (c : ℚ) (m n : ℕ) :
    globalFabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicTranslatedFormula c m n : ℝ) := by
  simpa only [globalFabius] using
    extendedFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
      fabius fabius_spec c m n

/-- Bounded-function arbitrary-translation formula on the unit interval. -/
theorem fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    (F : BoundedFabius) (hF : IsFabius F) (c : ℚ) (m n : ℕ)
    (hm : m ≤ 2 ^ n) :
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicTranslatedFormula c m n : ℝ) := by
  calc
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
        (fabiusDyadic n m : ℝ) := (fabiusDyadic_cast F hF n m hm).symm
    _ = (qBinomialThueMorseDyadicTranslatedFormula c m n : ℝ) := by
      rw [fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula]

/-- Canonical bounded arbitrary-translation formula on the unit interval. -/
theorem fabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    (c : ℚ) (m n : ℕ) (hm : m ≤ 2 ^ n) :
    fabiusReal fabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicTranslatedFormula c m n : ℝ) :=
  fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    fabius fabius_spec c m n hm

/-- The fully displayed canonical signed-global identity for an arbitrary
rational translation `q`. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadic_translated_sum
    (q : ℚ) (m n : ℕ) :
    globalFabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (((1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((2 : ℚ) ^ (k * (k - 1)) * ((n + k).factorial : ℚ)) *
            ∑ j ∈ Finset.range (m * 2 ^ k),
              (thueMorseSign j : ℚ) *
                ((j : ℚ) - (m : ℚ) * (2 : ℚ) ^ k + q) ^
                  (n + k) : ℚ) : ℝ) := by
  rw [globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    q m n]
  simp only [qBinomialThueMorseDyadicTranslatedFormula,
    thueMorseDyadicNumeratorTranslatedPowerSum, four_pow_choose_two]

/-- The fully displayed arbitrary-rational-translation identity for every
bounded Fabius function on the unit dyadic interval. -/
theorem fabiusFunction_dyadic_eq_qBinomialThueMorseDyadic_translated_sum
    (F : BoundedFabius) (hF : IsFabius F) (q : ℚ) (m n : ℕ)
    (hm : m ≤ 2 ^ n) :
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
      (((1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((2 : ℚ) ^ (k * (k - 1)) * ((n + k).factorial : ℚ)) *
            ∑ j ∈ Finset.range (m * 2 ^ k),
              (thueMorseSign j : ℚ) *
                ((j : ℚ) - (m : ℚ) * (2 : ℚ) ^ k + q) ^
                  (n + k) : ℚ) : ℝ) := by
  rw [fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    F hF q m n hm]
  simp only [qBinomialThueMorseDyadicTranslatedFormula,
    thueMorseDyadicNumeratorTranslatedPowerSum, four_pow_choose_two]

/-- Canonical bounded-Fabius specialization of the fully displayed
arbitrary-rational-translation identity. -/
theorem fabius_dyadic_eq_qBinomialThueMorseDyadic_translated_sum
    (q : ℚ) (m n : ℕ) (hm : m ≤ 2 ^ n) :
    fabiusReal fabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (((1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          qBinomial n k (1 / 2) /
              ((2 : ℚ) ^ (k * (k - 1)) * ((n + k).factorial : ℚ)) *
            ∑ j ∈ Finset.range (m * 2 ^ k),
              (thueMorseSign j : ℚ) *
                ((j : ℚ) - (m : ℚ) * (2 : ℚ) ^ k + q) ^
                  (n + k) : ℚ) : ℝ) := by
  rw [fabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
    q m n hm]
  simp only [qBinomialThueMorseDyadicTranslatedFormula,
    thueMorseDyadicNumeratorTranslatedPowerSum, four_pow_choose_two]

/-- Global real-valued unshifted formula. -/
theorem extendedFabius_dyadic_eq_qBinomialThueMorseDyadicFormula
    (F : BoundedFabius) (hF : IsFabius F) (m n : ℕ) :
    extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicFormula m n : ℝ) := by
  calc
    extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) =
        (fabiusDyadic n m : ℝ) :=
      (fabiusDyadic_cast_extended_nat F hF n m).symm
    _ = (qBinomialThueMorseDyadicFormula m n : ℝ) := by
      rw [fabiusDyadic_eq_qBinomialThueMorseDyadicFormula]

/-- Canonical signed-global unshifted formula. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadicFormula
    (m n : ℕ) :
    globalFabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicFormula m n : ℝ) := by
  simpa only [globalFabius] using
    extendedFabius_dyadic_eq_qBinomialThueMorseDyadicFormula
      fabius fabius_spec m n

/-- Bounded-function unshifted formula on the unit interval. -/
theorem fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicFormula
    (F : BoundedFabius) (hF : IsFabius F) (m n : ℕ)
    (hm : m ≤ 2 ^ n) :
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicFormula m n : ℝ) := by
  calc
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
        (fabiusDyadic n m : ℝ) := (fabiusDyadic_cast F hF n m hm).symm
    _ = (qBinomialThueMorseDyadicFormula m n : ℝ) := by
      rw [fabiusDyadic_eq_qBinomialThueMorseDyadicFormula]

/-- Canonical bounded unshifted formula on the unit interval. -/
theorem fabius_dyadic_eq_qBinomialThueMorseDyadicFormula
    (m n : ℕ) (hm : m ≤ 2 ^ n) :
    fabiusReal fabius ((m : ℝ) / (2 : ℝ) ^ n) =
      (qBinomialThueMorseDyadicFormula m n : ℝ) :=
  fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicFormula
    fabius fabius_spec m n hm

/-- The arbitrary translated finite formula depends only on the represented
dyadic rational.  The two representations may use different common
translations as well as different numerators and denominator exponents. -/
theorem qBinomialThueMorseDyadicTranslatedFormula_eq_of_rat_eq
    (q₁ q₂ : ℚ) (n₁ n₂ m₁ m₂ : ℕ)
    (h : (m₁ : ℚ) / (2 : ℚ) ^ n₁ =
      (m₂ : ℚ) / (2 : ℚ) ^ n₂) :
    qBinomialThueMorseDyadicTranslatedFormula q₁ m₁ n₁ =
      qBinomialThueMorseDyadicTranslatedFormula q₂ m₂ n₂ := by
  rw [← fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula,
    ← fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula,
    fabiusDyadic_eq_extendedFabiusDyadicValue_nat,
    fabiusDyadic_eq_extendedFabiusDyadicValue_nat]
  apply extendedFabiusDyadicValue_eq_of_rat_eq n₁ n₂ (m₁ : ℤ) (m₂ : ℤ)
  norm_num only [Int.cast_natCast]
  exact h

/-- The translated finite formula splits canonically into its dyadic block sign
and the formula at the remainder.  The two translation parameters may differ:
both formulas represent the same translation-independent Fabius values. -/
theorem qBinomialThueMorseDyadicTranslatedFormula_eq_block_sign_mul_mod
    (q₁ q₂ : ℚ) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormula q₁ m n =
      (thueMorseSign (m / 2 ^ (n + 1)) : ℚ) *
        qBinomialThueMorseDyadicTranslatedFormula q₂
          (m % 2 ^ (n + 1)) n := by
  calc
    qBinomialThueMorseDyadicTranslatedFormula q₁ m n = fabiusDyadic n m :=
      (fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula q₁ m n).symm
    _ = (thueMorseSign (m / 2 ^ (n + 1)) : ℚ) *
          fabiusDyadic n (m % 2 ^ (n + 1)) :=
      fabiusDyadic_eq_block_sign_mul_mod n m
    _ = (thueMorseSign (m / 2 ^ (n + 1)) : ℚ) *
          qBinomialThueMorseDyadicTranslatedFormula q₂
            (m % 2 ^ (n + 1)) n := by
      rw [fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula
        q₂ (m % 2 ^ (n + 1)) n]

/-- A single dyadic refinement leaves the translated formula unchanged, even
if its common translation is changed at the same time. -/
theorem qBinomialThueMorseDyadicTranslatedFormula_refine
    (q₁ q₂ : ℚ) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormula q₁ (2 * m) (n + 1) =
      qBinomialThueMorseDyadicTranslatedFormula q₂ m n := by
  rw [← fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula,
    ← fabiusDyadic_eq_qBinomialThueMorseDyadicTranslatedFormula]
  exact fabiusDyadic_refine_of_kernel dyadicKernel_has_refinement n m

/-- The centered arbitrary-dyadic formula is independent of the chosen
numerator and denominator exponent. -/
theorem qBinomialThueMorseDyadicFormula_eq_of_rat_eq
    (n₁ n₂ m₁ m₂ : ℕ)
    (h : (m₁ : ℚ) / (2 : ℚ) ^ n₁ =
      (m₂ : ℚ) / (2 : ℚ) ^ n₂) :
    qBinomialThueMorseDyadicFormula m₁ n₁ =
      qBinomialThueMorseDyadicFormula m₂ n₂ := by
  simpa only [qBinomialThueMorseDyadicTranslatedFormula_eq_centered] using
    qBinomialThueMorseDyadicTranslatedFormula_eq_of_rat_eq
      0 0 n₁ n₂ m₁ m₂ h

/-- Doubling numerator and denominator leaves the centered arbitrary-dyadic
formula unchanged. -/
theorem qBinomialThueMorseDyadicFormula_refine (m n : ℕ) :
    qBinomialThueMorseDyadicFormula (2 * m) (n + 1) =
      qBinomialThueMorseDyadicFormula m n := by
  simpa only [qBinomialThueMorseDyadicTranslatedFormula_eq_centered] using
    qBinomialThueMorseDyadicTranslatedFormula_refine 0 0 m n

/-- Doubling numerator and denominator leaves the source half-shifted
expression unchanged. -/
theorem qBinomialThueMorseDyadicHalfShiftFormula_refine (m n : ℕ) :
    qBinomialThueMorseDyadicHalfShiftFormula (2 * m) (n + 1) =
      qBinomialThueMorseDyadicHalfShiftFormula m n := by
  simpa only [qBinomialThueMorseDyadicHalfShiftFormula] using
    qBinomialThueMorseDyadicTranslatedFormula_refine
      (1 / 2) (1 / 2) m n

/-- The half-shifted expression depends only on the represented dyadic
rational, not on the chosen numerator and denominator exponent. -/
theorem qBinomialThueMorseDyadicHalfShiftFormula_eq_of_rat_eq
    (n₁ n₂ m₁ m₂ : ℕ)
    (h : (m₁ : ℚ) / (2 : ℚ) ^ n₁ =
      (m₂ : ℚ) / (2 : ℚ) ^ n₂) :
    qBinomialThueMorseDyadicHalfShiftFormula m₁ n₁ =
      qBinomialThueMorseDyadicHalfShiftFormula m₂ n₂ := by
  simpa only [qBinomialThueMorseDyadicHalfShiftFormula] using
    qBinomialThueMorseDyadicTranslatedFormula_eq_of_rat_eq
      (1 / 2) (1 / 2) n₁ n₂ m₁ m₂ h


end

end Fabius
