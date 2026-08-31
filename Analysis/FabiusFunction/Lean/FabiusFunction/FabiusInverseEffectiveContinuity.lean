import FabiusFunction.FabiusComputability
import FabiusFunction.FabiusRecurrenceSequence
import FabiusFunction.InverseModulus

/-!
# Effective continuity of the inverse Fabius function

The exact inverse modulus says that an input radius `F h` is both sufficient
and optimal for forcing inverse-output error below `h`.  This module makes the
sufficient direction fully effective at dyadic output scales.

Keeping the zeroth term of the exact inverse-dyadic recurrence first gives a
strong one-term lower bound for `F (2⁻ʳ)`.  Replacing `2 ^ r - 1` by
`2 ^ r` yields the executable factorial denominator

`2 ^ ((r + 1).choose 2) * (r + 1)!`.

This is stronger than the elementary box-event denominator

`2 ^ ((r + 1).choose 2) * (r + 1) ^ (r + 1)`

from the inverse-computability report.  Both therefore give certified inverse
moduli.  The factorial denominator is primitive recursive and, with the
simple choice `r = n`, packages the effective-uniform-continuity half of
computability for the totalized inverse.  No sequential-computability claim
is made here; that requires a separate tolerant-bisection realizer.
-/

set_option autoImplicit false

open Finset Set

namespace Fabius

private theorem natPow_primrec : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem choose_succ_two_eq_triangle (r : ℕ) :
    (r + 1).choose 2 = r * (r + 1) / 2 := by
  have h : r + 1 - 1 = r := by omega
  rw [Nat.choose_two_right, h, Nat.mul_comm (r + 1) r]

/-! ## Executable dyadic denominators -/

/-- The stronger factorial denominator for inverse output tolerance `2⁻ʳ`.

It is defined recursively so its primitive recursiveness is immediate;
`inverseFabiusFactorialDenominator_eq` gives the closed form
`2 ^ ((r + 1).choose 2) * (r + 1)!`. -/
def inverseFabiusFactorialDenominator : ℕ → ℕ
  | 0 => 1
  | r + 1 =>
      inverseFabiusFactorialDenominator r * 2 ^ (r + 1) * (r + 2)

/-- Closed form of the factorial inverse-modulus denominator. -/
theorem inverseFabiusFactorialDenominator_eq (r : ℕ) :
    inverseFabiusFactorialDenominator r =
      2 ^ (r + 1).choose 2 * (r + 1).factorial := by
  induction r with
  | zero => norm_num [inverseFabiusFactorialDenominator]
  | succ r ih =>
      rw [inverseFabiusFactorialDenominator, ih]
      have hchoose : (r + 2).choose 2 = (r + 1).choose 2 + (r + 1) := by
        simp [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [hchoose, pow_add,
        show (r + 2).factorial = (r + 2) * (r + 1).factorial by
          rw [Nat.factorial_succ]]
      ring

private theorem inverseFabiusFactorialDenominatorStep_primrec :
    Primrec₂ (fun r d : ℕ => d * 2 ^ (r + 1) * (r + 2)) := by
  exact Primrec.nat_mul.comp₂
    (Primrec.nat_mul.comp₂ Primrec₂.right
      (natPow_primrec.comp₂ (Primrec.const 2).to₂
        (Primrec.succ.comp₂ Primrec₂.left)))
    (Primrec.succ.comp₂ (Primrec.succ.comp₂ Primrec₂.left))

/-- The factorial inverse-modulus denominator is primitive recursive. -/
theorem inverseFabiusFactorialDenominator_primrec :
    Primrec inverseFabiusFactorialDenominator := by
  exact (Primrec.nat_rec₁ 1
    inverseFabiusFactorialDenominatorStep_primrec).of_eq fun r => by
      induction r with
      | zero => rfl
      | succ r ih =>
          simp only [inverseFabiusFactorialDenominator]
          rw [ih]

/-- The elementary box-event denominator from the inverse-computability
report.  Its reciprocal is
`2 ^ (-r(r+1)/2) * (r+1) ^ (-(r+1))`. -/
def inverseFabiusDeltaDenominator (r : ℕ) : ℕ :=
  2 ^ (r + 1).choose 2 * (r + 1) ^ (r + 1)

/-- The report's elementary box-event denominator is primitive recursive. -/
theorem inverseFabiusDeltaDenominator_primrec :
    Primrec inverseFabiusDeltaDenominator := by
  have hsucc : Primrec (fun r : ℕ => r + 1) := Primrec.succ
  have htriangle : Primrec (fun r : ℕ => r * (r + 1) / 2) :=
    Primrec.nat_div.comp
      (Primrec.nat_mul.comp Primrec.id hsucc) (Primrec.const 2)
  have hpowTwo : Primrec (fun r : ℕ => 2 ^ (r * (r + 1) / 2)) :=
    natPow_primrec.comp (Primrec.const 2) htriangle
  have hpower : Primrec (fun r : ℕ => (r + 1) ^ (r + 1)) :=
    natPow_primrec.comp hsucc hsucc
  exact (Primrec.nat_mul.comp hpowTwo hpower).of_eq fun r => by
    rw [inverseFabiusDeltaDenominator, choose_succ_two_eq_triangle]

/-! ## Endpoint-mass lower bounds -/

/-- Keeping only the positive zeroth term of the exact recurrence gives the
strongest elementary one-term lower bound used in this module. -/
theorem fabiusReal_inverse_two_pow_one_term_lower_bound
    (F : BoundedFabius) (hF : IsFabius F) {r : ℕ} (hr : 0 < r) :
    ((2 : ℝ) ^ r.choose 2 * ((r + 1).factorial : ℝ) *
      ((2 : ℝ) ^ r - 1))⁻¹ ≤
      fabiusReal F (((2 : ℝ) ^ r)⁻¹) := by
  have hdenQ : (0 : ℚ) < (2 : ℚ) ^ r - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) hr.ne')
  have hsumQ :
      (1 : ℚ) / ((r + 1).factorial : ℚ) ≤
        ∑ k ∈ range r,
          fabiusRecurrenceSequence k /
            (((r - k + 1).factorial : ℕ) : ℚ) := by
    have hsingle := Finset.single_le_sum
      (s := range r)
      (f := fun k => fabiusRecurrenceSequence k /
        (((r - k + 1).factorial : ℕ) : ℚ))
      (fun k _hk => (div_pos (fabiusRecurrenceSequence_pos k)
        (by positivity)).le)
      (show 0 ∈ range r by simpa using hr)
    simpa [fabiusRecurrenceSequence_zero] using hsingle
  have haQ :
      ((1 : ℚ) / ((r + 1).factorial : ℚ)) /
          ((2 : ℚ) ^ r - 1) ≤ fabiusRecurrenceSequence r := by
    rw [fabiusRecurrenceSequence_recurrence r hr]
    exact (div_le_div_iff_of_pos_right hdenQ).2 hsumQ
  have haR :
      ((1 : ℝ) / ((r + 1).factorial : ℝ)) /
          ((2 : ℝ) ^ r - 1) ≤
        (fabiusRecurrenceSequence r : ℝ) := by
    have haCast := Rat.cast_mono (K := ℝ) haQ
    push_cast at haCast
    simpa using haCast
  rw [fabius_inverse_two_pow_eq_recurrenceSequence F hF r]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hsub : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) hr.ne')
  calc
    ((2 : ℝ) ^ r.choose 2 * ((r + 1).factorial : ℝ) *
        ((2 : ℝ) ^ r - 1))⁻¹ =
        ((2 : ℝ) ^ r.choose 2)⁻¹ *
          (((1 : ℝ) / ((r + 1).factorial : ℝ)) /
            ((2 : ℝ) ^ r - 1)) := by
      field_simp
    _ ≤ ((2 : ℝ) ^ r.choose 2)⁻¹ *
        (fabiusRecurrenceSequence r : ℝ) :=
      mul_le_mul_of_nonneg_left haR (by positivity)

/-- The recurrence lower bound with `2 ^ r - 1` replaced by `2 ^ r`.
Equivalently, the reciprocal of the executable factorial denominator is a
certified lower bound for the dyadic endpoint mass. -/
theorem inv_inverseFabiusFactorialDenominator_le_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    ((inverseFabiusFactorialDenominator r : ℝ))⁻¹ ≤
      fabiusReal F (((2 : ℝ) ^ r)⁻¹) := by
  cases r with
  | zero =>
      norm_num [inverseFabiusFactorialDenominator, hF.one_of_one_le]
  | succ r =>
      have hr : 0 < r + 1 := by omega
      have hone := fabiusReal_inverse_two_pow_one_term_lower_bound F hF hr
      have hchoose : (r + 2).choose 2 = (r + 1).choose 2 + (r + 1) := by
        simp [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      have hdenle :
          (2 : ℝ) ^ (r + 1).choose 2 * ((r + 2).factorial : ℝ) *
              ((2 : ℝ) ^ (r + 1) - 1) ≤
            (inverseFabiusFactorialDenominator (r + 1) : ℝ) := by
        rw [inverseFabiusFactorialDenominator_eq]
        push_cast
        have hfactor :
            (2 : ℝ) ^ (r + 2).choose 2 =
              (2 : ℝ) ^ (r + 1).choose 2 * (2 : ℝ) ^ (r + 1) := by
          rw [hchoose, pow_add]
        rw [hfactor]
        calc
          (2 : ℝ) ^ (r + 1).choose 2 * ↑(r + 2).factorial *
                ((2 : ℝ) ^ (r + 1) - 1) ≤
              (2 : ℝ) ^ (r + 1).choose 2 * ↑(r + 2).factorial *
                (2 : ℝ) ^ (r + 1) :=
            mul_le_mul_of_nonneg_left
              (sub_le_self ((2 : ℝ) ^ (r + 1)) (by norm_num))
              (mul_nonneg (by positivity) (by positivity))
          _ = (2 : ℝ) ^ (r + 1).choose 2 *
                2 ^ (r + 1) * ↑(r + 2).factorial := by ring
      have hleftPos :
          0 < (2 : ℝ) ^ (r + 1).choose 2 * ((r + 2).factorial : ℝ) *
            ((2 : ℝ) ^ (r + 1) - 1) := by
        exact mul_pos (mul_pos (by positivity) (by positivity))
          (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))
      have hrightPos :
          0 < (inverseFabiusFactorialDenominator (r + 1) : ℝ) := by
        rw [inverseFabiusFactorialDenominator_eq]
        positivity
      exact ((inv_le_inv₀ hrightPos hleftPos).2 hdenle).trans hone

/-- The factorial denominator is no larger than the report's elementary
box-event denominator. -/
theorem inverseFabiusFactorialDenominator_le_deltaDenominator
    (r : ℕ) :
    inverseFabiusFactorialDenominator r ≤
      inverseFabiusDeltaDenominator r := by
  rw [inverseFabiusFactorialDenominator_eq,
    inverseFabiusDeltaDenominator]
  exact Nat.mul_le_mul_left _ (Nat.factorial_le_pow (r + 1))

/-- The report's box-event lower bound follows from the stronger recurrence
and factorial estimate, without formalizing an infinite-product cylinder. -/
theorem inv_inverseFabiusDeltaDenominator_le_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    ((inverseFabiusDeltaDenominator r : ℝ))⁻¹ ≤
      fabiusReal F (((2 : ℝ) ^ r)⁻¹) := by
  have hle :
      (inverseFabiusFactorialDenominator r : ℝ) ≤
        inverseFabiusDeltaDenominator r := by
    exact_mod_cast inverseFabiusFactorialDenominator_le_deltaDenominator r
  have hfactorialPos :
      0 < (inverseFabiusFactorialDenominator r : ℝ) := by
    rw [inverseFabiusFactorialDenominator_eq]
    positivity
  have hdeltaPos : 0 < (inverseFabiusDeltaDenominator r : ℝ) := by
    rw [inverseFabiusDeltaDenominator]
    positivity
  exact ((inv_le_inv₀ hdeltaPos hfactorialPos).2 hle).trans
    (inv_inverseFabiusFactorialDenominator_le_fabiusReal F hF r)

/-! ## Effective inverse moduli -/

private theorem inverse_two_pow_mem_Icc (r : ℕ) :
    ((2 : ℝ) ^ r)⁻¹ ∈ Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))

/-- The stronger factorial-denominator dyadic inverse modulus. -/
theorem abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_factorialDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) {u v : ℝ}
    (huv : |u - v| <
      ((inverseFabiusFactorialDenominator r : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < ((2 : ℝ) ^ r)⁻¹ := by
  apply abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal F hF
    (inverse_two_pow_mem_Icc r)
  exact huv.trans_le
    (inv_inverseFabiusFactorialDenominator_le_fabiusReal F hF r)

/-- Closed-threshold companion to the factorial-denominator dyadic inverse
modulus.  This form is suited to certified interval algorithms. -/
theorem abs_fabiusInv_sub_le_inverse_two_pow_of_le_factorialDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) {u v : ℝ}
    (huv : |u - v| ≤
      ((inverseFabiusFactorialDenominator r : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| ≤ ((2 : ℝ) ^ r)⁻¹ := by
  apply abs_fabiusInv_sub_le_of_abs_sub_le_fabiusReal F hF
    (inverse_two_pow_mem_Icc r)
  exact huv.trans
    (inv_inverseFabiusFactorialDenominator_le_fabiusReal F hF r)

/-- The manuscript's strict-threshold explicit dyadic inverse modulus. -/
theorem abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_deltaDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) {u v : ℝ}
    (huv : |u - v| < ((inverseFabiusDeltaDenominator r : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < ((2 : ℝ) ^ r)⁻¹ := by
  apply abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal F hF
    (inverse_two_pow_mem_Icc r)
  exact huv.trans_le
    (inv_inverseFabiusDeltaDenominator_le_fabiusReal F hF r)

/-- Closed-threshold companion to the manuscript's elementary dyadic inverse
modulus. -/
theorem abs_fabiusInv_sub_le_inverse_two_pow_of_le_deltaDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) {u v : ℝ}
    (huv : |u - v| ≤ ((inverseFabiusDeltaDenominator r : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| ≤ ((2 : ℝ) ^ r)⁻¹ := by
  apply abs_fabiusInv_sub_le_of_abs_sub_le_fabiusReal F hF
    (inverse_two_pow_mem_Icc r)
  exact huv.trans
    (inv_inverseFabiusDeltaDenominator_le_fabiusReal F hF r)

/-- The totalized inverse Fabius function is effectively uniformly
continuous.  The primitive-recursive witness is the stronger factorial
denominator at order `n`; `n < 2 ^ n` converts its dyadic output bound to the
reciprocal convention required by `EffectivelyUniformContinuous`. -/
theorem fabiusInv_effectivelyUniformContinuous
    (F : BoundedFabius) (hF : IsFabius F) :
    EffectivelyUniformContinuous (fabiusInv F hF) := by
  refine ⟨inverseFabiusFactorialDenominator,
    inverseFabiusFactorialDenominator_primrec.to_comp, ?_, ?_⟩
  · intro n _hn
    rw [inverseFabiusFactorialDenominator_eq]
    positivity
  · intro n hn u v huv
    have hdyadic :=
      abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_factorialDenominator
        F hF n (by simpa only [one_div] using huv)
    have hpow : (n : ℝ) < (2 : ℝ) ^ n := by
      exact_mod_cast Nat.lt_two_pow_self (n := n)
    have hinv : ((2 : ℝ) ^ n)⁻¹ < (n : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by exact_mod_cast hn)).2 hpow
    exact hdyadic.trans (by simpa only [one_div] using hinv)

end Fabius
