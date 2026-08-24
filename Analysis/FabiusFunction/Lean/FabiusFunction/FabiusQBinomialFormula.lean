import FabiusFunction.FabiusRecurrenceSequence
import FabiusFunction.HalfQBinomial
import FabiusFunction.ThueMorseExponential

/-!
# A q-binomial--Thue--Morse formula for dyadic Fabius values

This module proves the Wolfram Language identity

`FabiusF[2^(-n)] = 1 / (2^(n^2) QPochhammer[1/2,1/2,n])` times

`Sum[QBinomial[n,k,1/2] / (4^Binomial[k,2] (n+k)!)` times
`Sum[(-1)^ThueMorse[r] (r-2^k)^(n+k), {r,0,2^k-1}], {k,0,n}]`.

The inner subtraction is performed in `ℚ`, as it is in Wolfram Language.
The theorem includes `n = 0`.
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

private theorem choose_square_split (n : ℕ) :
    n * n = (n + 1).choose 2 + n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htop : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.choose_one_right]
        omega
      have hbottom : (n + 1).choose 2 = n.choose 2 + n := by
        rw [show n + 1 = n + 1 by rfl,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.choose_one_right]
        omega
      rw [htop, hbottom]
      nlinarith

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

end

end Fabius
