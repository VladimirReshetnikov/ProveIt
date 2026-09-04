import FabiusFunction.CumulantBellFormula
import FabiusFunction.ExponentialBell
import FabiusFunction.FallingFactorialSeries
import FabiusFunction.InverseBellCoefficients
import FabiusFunction.OrdinaryBellComposition

/-!
# Bell-polynomial coefficients of powers, logarithms, and exponentials

This module joins the ordinary and exponential Bell-polynomial conventions
used in the transseries manuscripts. If `x j` is the coefficient of `X^j`,
then the ordinary partial Bell polynomial is the factorial normalization of
the exponential partial Bell polynomial evaluated at `j! * x j`.

The conversion turns the general composition theorem into coefficient
formulas for `(1+w)^β`, negative integral powers, and `log (1+w)`. A final
group of results identifies the coefficients of `exp D` with the unordered
weighted-partition sum and records its triangular recurrence. Everything is
formal algebra over a commutative rational algebra; no analytic convergence
or choice of a logarithm branch is involved.

## Main declarations

* `ordPartialBell_eq_factorialRatio_partialBell` is the ordinary/exponential
  Bell normalization.
* `coeff_fallingSeries_subst_eq_sum_ordPartialBell` gives arbitrary formal
  powers of a unit series.
* `coeff_negBinomSeries_subst_eq_sum_ordPartialBell` gives negative integral
  powers.
* `coeff_logOf_eq_sum_ordPartialBell` gives logarithmic coefficients.
* `coeff_exp_subst_eq_partitionExpSum` and its companions give exponential
  jets, their multiplicity-vector formula, and their recurrence.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

noncomputable section

namespace Fabius

section BellConversion

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- **Ordinary/exponential Bell conversion.** The ordinary partial Bell
polynomial in the coefficient sequence `x` is `k! / n!` times the
exponential partial Bell polynomial in the factorially weighted sequence. -/
theorem ordPartialBell_eq_factorialRatio_partialBell
    (x : ℕ → A) (n k : ℕ) :
    ordPartialBell x n k =
      algebraMap ℚ A ((k.factorial : ℚ) / n.factorial) *
        partialBell (fun j => (j.factorial : A) * x j) n k := by
  let y : ℕ → A := fun j => (j.factorial : A) * x j
  have hcoeff {j : ℕ} (hj : 1 ≤ j) :
      coeff j (bellWeightSeries A y) = x j := by
    rw [bellWeightSeries, coeff_egfA, if_neg (Nat.ne_of_gt hj)]
    dsimp [y]
    rw [show (j.factorial : A) = algebraMap ℚ A (j.factorial : ℚ) by simp]
    rw [← mul_assoc, ← map_mul, one_div_mul_cancel (by positivity), map_one,
      one_mul]
  have hord :
      ordPartialBell (fun j => coeff j (bellWeightSeries A y)) n k =
        ordPartialBell x n k :=
    ordPartialBell_congr (fun j hj => hcoeff hj) n k
  have hpow := coeff_pow_eq_ordPartialBell
    (constantCoeff_bellWeightSeries A y) n k
  rw [coeff_bellWeightSeries_pow, hord] at hpow
  calc
    ordPartialBell x n k =
        (k.factorial : A) *
          (algebraMap ℚ A (1 / n.factorial) * partialBell y n k) := hpow.symm
    _ = algebraMap ℚ A ((k.factorial : ℚ) / n.factorial) *
          partialBell y n k := by
      rw [show (k.factorial : A) =
        algebraMap ℚ A (k.factorial : ℚ) by simp, ← mul_assoc, ← map_mul]
      congr 2
      ring

/-- Denominator-cleared form of the ordinary/exponential Bell conversion. -/
theorem factorial_mul_ordPartialBell_eq_factorial_mul_partialBell
    (x : ℕ → A) (n k : ℕ) :
    (n.factorial : A) * ordPartialBell x n k =
      (k.factorial : A) *
        partialBell (fun j => (j.factorial : A) * x j) n k := by
  rw [ordPartialBell_eq_factorialRatio_partialBell A]
  rw [show (n.factorial : A) = algebraMap ℚ A (n.factorial : ℚ) by simp,
    show (k.factorial : A) = algebraMap ℚ A (k.factorial : ℚ) by simp]
  rw [← mul_assoc, ← map_mul]
  congr 2
  field_simp

end BellConversion

section UnitPowers

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Coefficients of the formal power `(1+w)^β`, expressed with ordinary
partial Bell polynomials. -/
theorem coeff_fallingSeries_subst_eq_sum_ordPartialBell
    {w : A⟦X⟧} (hw : constantCoeff w = 0) (β : A) (n : ℕ) :
    coeff n ((fallingSeries A β).subst w) =
      ∑ k ∈ range (n + 1),
        (algebraMap ℚ A (1 / k.factorial) *
          (descPochhammer A k).eval β) *
            ordPartialBell (fun r => coeff r w) n k := by
  rw [coeff_subst_eq_sum_ordPartialBell _ hw]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [fallingSeries, coeff_egfA]

/-- Exponential-Bell form of the coefficients of the formal power
`(1 + w)^β`. The theorem is valid also in degree zero. -/
theorem coeff_fallingSeries_subst_eq_sum_partialBell
    {w : A⟦X⟧} (hw : constantCoeff w = 0) (β : A) (n : ℕ) :
    coeff n ((fallingSeries A β).subst w) =
      algebraMap ℚ A (1 / n.factorial) *
        ∑ k ∈ range (n + 1),
          (descPochhammer A k).eval β *
            partialBell (fun r => (r.factorial : A) * coeff r w) n k := by
  rw [coeff_fallingSeries_subst_eq_sum_ordPartialBell A hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [ordPartialBell_eq_factorialRatio_partialBell A]
  have hrat :
      (1 / (k.factorial : ℚ)) * ((k.factorial : ℚ) / n.factorial) =
        1 / n.factorial := by
    field_simp
  calc
    (algebraMap ℚ A (1 / k.factorial) * (descPochhammer A k).eval β) *
          (algebraMap ℚ A ((k.factorial : ℚ) / n.factorial) *
            partialBell (fun r => (r.factorial : A) * coeff r w) n k) =
        (algebraMap ℚ A (1 / k.factorial) *
          algebraMap ℚ A ((k.factorial : ℚ) / n.factorial)) *
            ((descPochhammer A k).eval β *
              partialBell (fun r => (r.factorial : A) * coeff r w) n k) := by
      ring
    _ = algebraMap ℚ A (1 / n.factorial) *
          ((descPochhammer A k).eval β *
            partialBell (fun r => (r.factorial : A) * coeff r w) n k) := by
      rw [← map_mul, hrat]

omit [Algebra ℚ A] in
/-- Coefficients of `(1+w)^(-(d+1))`, expressed with ordinary partial Bell
polynomials. -/
theorem coeff_negBinomSeries_subst_eq_sum_ordPartialBell
    {w : A⟦X⟧} (hw : constantCoeff w = 0) (d n : ℕ) :
    coeff n ((negBinomSeries A d).subst w) =
      ∑ k ∈ range (n + 1),
        ((-1 : A) ^ k * ((d + k).choose d : A)) *
          ordPartialBell (fun r => coeff r w) n k := by
  rw [coeff_subst_eq_sum_ordPartialBell _ hw]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coeff_negBinomSeries]

omit [Algebra ℚ A] in
/-- Manuscript indexing of the negative-integral-power formula:
`(1+w)^(-j)` has coefficient `(-1)^k * choose (j+k-1) k` in front of the
ordinary partial Bell polynomial. -/
theorem coeff_negBinomSeries_subst_eq_sum_ordPartialBell_of_pos
    {w : A⟦X⟧} (hw : constantCoeff w = 0)
    (j n : ℕ) (hj : 1 ≤ j) :
    coeff n ((negBinomSeries A (j - 1)).subst w) =
      ∑ k ∈ range (n + 1),
        ((-1 : A) ^ k * ((j + k - 1).choose k : A)) *
          ordPartialBell (fun r => coeff r w) n k := by
  rw [coeff_negBinomSeries_subst_eq_sum_ordPartialBell A hw]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 3
  rw [Nat.choose_symm_add]
  congr 1
  omega

/-- Coefficients of the formal logarithm of a unit series, in ordinary Bell
form. The range is exactly `1 ≤ k ≤ n`; in particular the formula also
covers the constant coefficient `n = 0`. -/
theorem coeff_logOf_eq_sum_ordPartialBell
    {U : A⟦X⟧} (hU : constantCoeff U = 1) (n : ℕ) :
    coeff n (logOf U) =
      ∑ k ∈ Ico 1 (n + 1),
        algebraMap ℚ A ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) *
          ordPartialBell (fun r => coeff r U) n k := by
  have hw : constantCoeff (U - 1) = 0 := by
    rw [map_sub, hU, map_one, sub_self]
  rw [PowerSeries.logOf_eq,
    coeff_subst_eq_sum_ordPartialBell (PowerSeries.log A) hw n]
  have hdrop :
      (∑ k ∈ range (n + 1), coeff k (PowerSeries.log A) *
          ordPartialBell (fun r => coeff r (U - 1)) n k) =
        ∑ k ∈ Ico 1 (n + 1), coeff k (PowerSeries.log A) *
          ordPartialBell (fun r => coeff r (U - 1)) n k := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n + 1),
      Nat.Ico_zero_eq_range, Finset.sum_range_one, PowerSeries.coeff_log,
      if_pos rfl, zero_mul, zero_add]
  rw [hdrop]
  apply Finset.sum_congr rfl
  intro k hk
  rw [PowerSeries.coeff_log,
    if_neg (Nat.ne_of_gt (Finset.mem_Ico.mp hk).1)]
  congr 1
  apply ordPartialBell_congr
  intro r hr
  rw [map_sub, PowerSeries.coeff_one,
    if_neg (Nat.ne_of_gt hr), sub_zero]

end UnitPowers

section ExponentialJets

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Reweighting the ordinary coefficients of a power series by `n!` and
forming their exponential generating series recovers the original series. -/
theorem egfA_factorialDenormalize_coeff_eq (U : A⟦X⟧) :
    egfA A (factorialDenormalize fun n => coeff n U) = U := by
  apply PowerSeries.ext
  intro n
  rw [coeff_egfA, factorialDenormalize, Algebra.smul_def]
  rw [← mul_assoc, ← map_mul, one_div_mul_cancel (by positivity), map_one,
    one_mul]

/-- Exponential-Bell form of the logarithmic coefficients of a unit series.
The factorially denormalized input is the sequence `(n! * [X^n] U)_n`. -/
theorem coeff_logOf_eq_sum_partialBell
    {U : A⟦X⟧} (hU : constantCoeff U = 1) (n : ℕ) :
    coeff n (logOf U) =
      algebraMap ℚ A (1 / n.factorial) *
        ∑ k ∈ Ico 1 (n + 1),
          (-1 : A) ^ (k - 1) * ((k - 1).factorial : A) *
            partialBell (factorialDenormalize fun r => coeff r U) n k := by
  let m : ℕ → A := factorialDenormalize fun r => coeff r U
  have hcoeff0 : coeff 0 U = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, hU]
  have hm0 : m 0 = 1 := by
    simpa only [m, factorialDenormalize, Nat.factorial_zero, Nat.cast_one,
      one_smul] using hcoeff0
  have hseries : egfA A m = U := egfA_factorialDenormalize_coeff_eq A U
  calc
    coeff n (logOf U) = coeff n (logOf (egfA A m)) := by rw [hseries]
    _ = algebraMap ℚ A (1 / n.factorial) * cumulantSum A m n :=
      coeff_logOf_egfA A m hm0 n
    _ = algebraMap ℚ A (1 / n.factorial) *
        ∑ k ∈ Ico 1 (n + 1),
          (-1 : A) ^ (k - 1) * ((k - 1).factorial : A) *
            partialBell (factorialDenormalize fun r => coeff r U) n k := by
      rfl

/-- Complete-Bell form of the coefficients of the formal exponential of a
zero-constant series. The Bell input is `(n! * [X^n] D)_n`. -/
theorem coeff_exp_subst_eq_completeBell
    {D : A⟦X⟧} (hD : constantCoeff D = 0) (n : ℕ) :
    coeff n ((PowerSeries.exp A).subst D) =
      algebraMap ℚ A (1 / n.factorial) *
        Bell.complete (factorialDenormalize fun r => coeff r D) n := by
  let d : ℕ → A := factorialDenormalize fun r => coeff r D
  have hcoeff0 : coeff 0 D = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, hD]
  have hd0 : d 0 = 0 := by
    simpa only [d, factorialDenormalize, Nat.factorial_zero, Nat.cast_one,
      one_smul] using hcoeff0
  have hseries : bellWeightSeries A d = D := by
    rw [← egfA_eq_bellWeightSeries A d hd0,
      egfA_factorialDenormalize_coeff_eq A D]
  calc
    coeff n ((PowerSeries.exp A).subst D) =
        coeff n ((PowerSeries.exp A).subst (bellWeightSeries A d)) := by
      rw [hseries]
    _ = algebraMap ℚ A (1 / n.factorial) * Bell.complete d n := by
      rw [exp_subst_bellWeightSeries, coeff_egfA]
    _ = algebraMap ℚ A (1 / n.factorial) *
        Bell.complete (factorialDenormalize fun r => coeff r D) n := by
      rfl

/-- Weighted-partition form of the coefficients of a formal exponential.
This is the finite sum over all multiplicity vectors of total weight `n`. -/
theorem coeff_exp_subst_eq_partitionExpSum
    {D : A⟦X⟧} (hD : constantCoeff D = 0) (n : ℕ) :
    coeff n ((PowerSeries.exp A).subst D) =
      partitionExpSum (fun r => coeff r D) n := by
  let E : ℕ → A := fun r => coeff r D
  have hE0 : E 0 = 0 := by
    change coeff 0 D = 0
    rw [coeff_zero_eq_constantCoeff_apply, hD]
  have hseries : SaddleExpansion.exponentSeries E = D := by
    apply PowerSeries.ext
    intro r
    rw [SaddleExpansion.coeff_exponentSeries]
  calc
    coeff n ((PowerSeries.exp A).subst D) =
        coeff n ((PowerSeries.exp A).subst
          (SaddleExpansion.exponentSeries E)) := by
      rw [hseries]
    _ = coeff n (SaddleExpansion.expSeries E) := by
      rw [SaddleExpansion.expSeries_eq_exp_subst E hE0]
    _ = SaddleExpansion.expCoeff E n := by
      rw [SaddleExpansion.coeff_expSeries]
    _ = partitionExpSum E n := by
      rw [partitionExpSum_eq_expCoeff]
    _ = partitionExpSum (fun r => coeff r D) n := by
      rfl

/-- Expanded multiplicity-vector formula for the coefficients of a formal
exponential, valid in every commutative rational algebra. -/
theorem coeff_exp_subst_eq_sum_weightedPartitions
    {D : A⟦X⟧} (hD : constantCoeff D = 0) (n : ℕ) :
    coeff n ((PowerSeries.exp A).subst D) =
      ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
        (((f j).factorial : ℚ)⁻¹) • (coeff j D) ^ f j := by
  rw [coeff_exp_subst_eq_partitionExpSum A hD, partitionExpSum]

/-- Triangular recurrence for the coefficients of a formal exponential:
`n A_n = ∑_{j=1}^n j d_j A_{n-j}`. -/
theorem coeff_exp_subst_recurrence
    {D : A⟦X⟧} (hD : constantCoeff D = 0) (n : ℕ) :
    (n : A) * coeff n ((PowerSeries.exp A).subst D) =
      ∑ j ∈ Icc 1 n, (j : A) * coeff j D *
        coeff (n - j) ((PowerSeries.exp A).subst D) := by
  simpa only [coeff_exp_subst_eq_partitionExpSum A hD] using
    partitionExpSum_recurrence (fun r => coeff r D) n

end ExponentialJets

end Fabius
