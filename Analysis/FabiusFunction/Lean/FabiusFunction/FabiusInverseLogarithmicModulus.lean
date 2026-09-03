import FabiusFunction.FabiusInverseEffectiveContinuity

/-!
# A logarithmic effective modulus for the inverse Fabius function

`FabiusInverseEffectiveContinuity.lean` uses dyadic order `n` to turn an
input tolerance into inverse-output tolerance `1 / n`.  This file closes the
smaller modulus stated in the inverse-computability report.

For positive `n`, the least dyadic order with `n < 2 ^ r` is
`Nat.log2 n + 1`.  We certify that order by a primitive-recursive bounded
search, compose it with both executable endpoint-mass denominators, and
transport the existing strict and closed dyadic inverse moduli.  The
factorial denominator is stronger than the report's elementary Delta
denominator; both are primitive recursive.

The exact-rational ceiling modulus and the tolerant-bisection realizer remain
separate tasks.  No sequential-computability claim is made here.
-/

set_option autoImplicit false

open Set

namespace Fabius

private theorem powTwo_le_primrec :
    PrimrecRel (fun n r : ℕ => 2 ^ r ≤ n) := by
  exact Primrec.nat_le.comp
    (primrec₂_nat_pow.comp (Primrec.const 2) Primrec.snd)
    Primrec.fst

/-! ## The least logarithmic dyadic order -/

/-- The least dyadic order strictly above a positive natural input.

The bounded-search presentation makes primitive recursiveness transparent;
`inverseFabiusLogarithmicOrder_eq_succ_log2` identifies it with the usual
binary length.  Its harmless value at zero is `1`. -/
def inverseFabiusLogarithmicOrder (n : ℕ) : ℕ :=
  Nat.findGreatest (fun r => 2 ^ r ≤ n) n + 1

/-- The bounded-search order is exactly `Nat.log2 n + 1`. -/
theorem inverseFabiusLogarithmicOrder_eq_succ_log2 (n : ℕ) :
    inverseFabiusLogarithmicOrder n = Nat.log2 n + 1 := by
  unfold inverseFabiusLogarithmicOrder
  congr 1
  by_cases hn : n = 0
  · subst n
    simp
  · apply le_antisymm
    · apply (Nat.le_log2 hn).2
      exact Nat.findGreatest_spec
        (P := fun r => 2 ^ r ≤ n) (m := 0) (Nat.zero_le n)
        (by simpa using (Nat.one_le_iff_ne_zero.2 hn))
    · apply Nat.le_findGreatest
      · exact ((Nat.lt_two_pow_self (n := Nat.log2 n)).trans_le
          (Nat.log2_self_le hn)).le
      · exact Nat.log2_self_le hn

/-- The least logarithmic dyadic order is primitive recursive. -/
theorem inverseFabiusLogarithmicOrder_primrec :
    Primrec inverseFabiusLogarithmicOrder := by
  unfold inverseFabiusLogarithmicOrder
  exact Primrec.succ.comp
    (Primrec.nat_findGreatest Primrec.id powTwo_le_primrec)

/-- For positive `n`, `inverseFabiusLogarithmicOrder n` is the least natural
`r` satisfying `n < 2 ^ r`. -/
theorem inverseFabiusLogarithmicOrder_isLeast (n : ℕ) (hn : 0 < n) :
    IsLeast {r : ℕ | n < 2 ^ r} (inverseFabiusLogarithmicOrder n) := by
  rw [inverseFabiusLogarithmicOrder_eq_succ_log2]
  constructor
  · exact Nat.lt_log2_self
  · intro r hr
    exact Nat.succ_le_iff.2 ((Nat.log2_lt hn.ne').2 hr)

/-- The least logarithmic dyadic order never exceeds the coarse choice `n`
at positive inputs. -/
theorem inverseFabiusLogarithmicOrder_le_self (n : ℕ) (hn : 0 < n) :
    inverseFabiusLogarithmicOrder n ≤ n :=
  (inverseFabiusLogarithmicOrder_isLeast n hn).2 Nat.lt_two_pow_self

/-! ## Primitive-recursive logarithmic denominators -/

/-- The stronger factorial endpoint-mass denominator evaluated at the least
logarithmic dyadic order.  The value at zero follows the modulus convention
`d(0) = 1`. -/
def inverseFabiusLogarithmicFactorialDenominator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      inverseFabiusFactorialDenominator
        (inverseFabiusLogarithmicOrder (n + 1))

/-- The report's elementary Delta denominator evaluated at the least
logarithmic dyadic order, again with `d(0) = 1`. -/
def inverseFabiusLogarithmicDeltaDenominator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      inverseFabiusDeltaDenominator
        (inverseFabiusLogarithmicOrder (n + 1))

/-- At positive inputs, the logarithmic factorial denominator is the original
factorial denominator evaluated at the least dyadic order. -/
theorem inverseFabiusLogarithmicFactorialDenominator_of_pos
    (n : ℕ) (hn : 0 < n) :
    inverseFabiusLogarithmicFactorialDenominator n =
      inverseFabiusFactorialDenominator
        (inverseFabiusLogarithmicOrder n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rfl

/-- At positive inputs, the logarithmic Delta denominator is the report's
original Delta denominator evaluated at the least dyadic order. -/
theorem inverseFabiusLogarithmicDeltaDenominator_of_pos
    (n : ℕ) (hn : 0 < n) :
    inverseFabiusLogarithmicDeltaDenominator n =
      inverseFabiusDeltaDenominator
        (inverseFabiusLogarithmicOrder n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rfl

/-- The logarithmic factorial denominator is primitive recursive. -/
theorem inverseFabiusLogarithmicFactorialDenominator_primrec :
    Primrec inverseFabiusLogarithmicFactorialDenominator := by
  exact (Primrec.nat_casesOn₁ 1
    (inverseFabiusFactorialDenominator_primrec.comp
      (inverseFabiusLogarithmicOrder_primrec.comp Primrec.succ))).of_eq
        fun n => by cases n <;> rfl

/-- The logarithmic Delta denominator is primitive recursive. -/
theorem inverseFabiusLogarithmicDeltaDenominator_primrec :
    Primrec inverseFabiusLogarithmicDeltaDenominator := by
  exact (Primrec.nat_casesOn₁ 1
    (inverseFabiusDeltaDenominator_primrec.comp
      (inverseFabiusLogarithmicOrder_primrec.comp Primrec.succ))).of_eq
        fun n => by cases n <;> rfl

/-- The logarithmic factorial denominator is no larger than the report's
logarithmic Delta denominator. -/
theorem inverseFabiusLogarithmicFactorialDenominator_le_deltaDenominator
    (n : ℕ) :
    inverseFabiusLogarithmicFactorialDenominator n ≤
      inverseFabiusLogarithmicDeltaDenominator n := by
  by_cases hn : n = 0
  · subst n
    simp [inverseFabiusLogarithmicFactorialDenominator,
      inverseFabiusLogarithmicDeltaDenominator]
  · rw [inverseFabiusLogarithmicFactorialDenominator_of_pos n
      (Nat.pos_of_ne_zero hn),
    inverseFabiusLogarithmicDeltaDenominator_of_pos n
      (Nat.pos_of_ne_zero hn)]
    exact inverseFabiusFactorialDenominator_le_deltaDenominator _

private theorem inverse_two_pow_logarithmicOrder_lt_inv_nat
    (n : ℕ) (hn : 0 < n) :
    ((2 : ℝ) ^ inverseFabiusLogarithmicOrder n)⁻¹ < (n : ℝ)⁻¹ := by
  have hpowNat := (inverseFabiusLogarithmicOrder_isLeast n hn).1
  have hpowReal : (n : ℝ) <
      (2 : ℝ) ^ inverseFabiusLogarithmicOrder n := by
    exact_mod_cast hpowNat
  exact (inv_lt_inv₀ (by positivity) (by exact_mod_cast hn)).2 hpowReal

/-! ## The logarithmic inverse moduli -/

/-- The stronger logarithmic factorial modulus with strict input threshold. -/
theorem abs_fabiusInv_sub_lt_inv_nat_of_lt_logarithmicFactorialDenominator
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n)
    {u v : ℝ}
    (huv : |u - v| <
      ((inverseFabiusLogarithmicFactorialDenominator n : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < (n : ℝ)⁻¹ := by
  have huv' : |u - v| <
      ((inverseFabiusFactorialDenominator
        (inverseFabiusLogarithmicOrder n) : ℝ))⁻¹ := by
    rw [← inverseFabiusLogarithmicFactorialDenominator_of_pos n hn]
    exact huv
  exact (abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_factorialDenominator
    F hF (inverseFabiusLogarithmicOrder n) huv').trans
      (inverse_two_pow_logarithmicOrder_lt_inv_nat n hn)

/-- Closed-input-threshold companion to the logarithmic factorial modulus.
The output conclusion remains strict because the selected dyadic scale is
strictly smaller than `1 / n`. -/
theorem abs_fabiusInv_sub_lt_inv_nat_of_le_logarithmicFactorialDenominator
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n)
    {u v : ℝ}
    (huv : |u - v| ≤
      ((inverseFabiusLogarithmicFactorialDenominator n : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < (n : ℝ)⁻¹ := by
  have huv' : |u - v| ≤
      ((inverseFabiusFactorialDenominator
        (inverseFabiusLogarithmicOrder n) : ℝ))⁻¹ := by
    rw [← inverseFabiusLogarithmicFactorialDenominator_of_pos n hn]
    exact huv
  exact (abs_fabiusInv_sub_le_inverse_two_pow_of_le_factorialDenominator
    F hF (inverseFabiusLogarithmicOrder n) huv').trans_lt
      (inverse_two_pow_logarithmicOrder_lt_inv_nat n hn)

/-- The report's logarithmic Delta modulus with strict input threshold. -/
theorem abs_fabiusInv_sub_lt_inv_nat_of_lt_logarithmicDeltaDenominator
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n)
    {u v : ℝ}
    (huv : |u - v| <
      ((inverseFabiusLogarithmicDeltaDenominator n : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < (n : ℝ)⁻¹ := by
  have huv' : |u - v| <
      ((inverseFabiusDeltaDenominator
        (inverseFabiusLogarithmicOrder n) : ℝ))⁻¹ := by
    rw [← inverseFabiusLogarithmicDeltaDenominator_of_pos n hn]
    exact huv
  exact (abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_deltaDenominator
    F hF (inverseFabiusLogarithmicOrder n) huv').trans
      (inverse_two_pow_logarithmicOrder_lt_inv_nat n hn)

/-- Closed-input-threshold companion to the report's logarithmic Delta
modulus. -/
theorem abs_fabiusInv_sub_lt_inv_nat_of_le_logarithmicDeltaDenominator
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n)
    {u v : ℝ}
    (huv : |u - v| ≤
      ((inverseFabiusLogarithmicDeltaDenominator n : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < (n : ℝ)⁻¹ := by
  have huv' : |u - v| ≤
      ((inverseFabiusDeltaDenominator
        (inverseFabiusLogarithmicOrder n) : ℝ))⁻¹ := by
    rw [← inverseFabiusLogarithmicDeltaDenominator_of_pos n hn]
    exact huv
  exact (abs_fabiusInv_sub_le_inverse_two_pow_of_le_deltaDenominator
    F hF (inverseFabiusLogarithmicOrder n) huv').trans_lt
      (inverse_two_pow_logarithmicOrder_lt_inv_nat n hn)

/-- Effective uniform continuity of the totalized inverse, now witnessed by
the smaller logarithmic factorial denominator. -/
theorem fabiusInv_effectivelyUniformContinuous_logarithmic
    (F : BoundedFabius) (hF : IsFabius F) :
    EffectivelyUniformContinuous (fabiusInv F hF) :=
  fabiusInv_effectivelyUniformContinuous_of_denominator F hF
    inverseFabiusLogarithmicFactorialDenominator
    inverseFabiusLogarithmicFactorialDenominator_primrec.to_comp
    (fun n hn => by
      rw [inverseFabiusLogarithmicFactorialDenominator_of_pos n hn,
        inverseFabiusFactorialDenominator_eq]
      positivity)
    (fun n hn => ⟨inverseFabiusLogarithmicOrder n,
      (inverseFabiusLogarithmicOrder_isLeast n hn).1, by
        rw [inverseFabiusLogarithmicFactorialDenominator_of_pos n hn]
        exact inv_inverseFabiusFactorialDenominator_le_fabiusReal F hF _⟩)

/-- Effective uniform continuity witnessed by the report-exact logarithmic
Delta denominator.  The factorial theorem above supplies the stronger
alternative. -/
theorem fabiusInv_effectivelyUniformContinuous_logarithmicDelta
    (F : BoundedFabius) (hF : IsFabius F) :
    EffectivelyUniformContinuous (fabiusInv F hF) :=
  fabiusInv_effectivelyUniformContinuous_of_denominator F hF
    inverseFabiusLogarithmicDeltaDenominator
    inverseFabiusLogarithmicDeltaDenominator_primrec.to_comp
    (fun n hn => by
      rw [inverseFabiusLogarithmicDeltaDenominator_of_pos n hn,
        inverseFabiusDeltaDenominator]
      positivity)
    (fun n hn => ⟨inverseFabiusLogarithmicOrder n,
      (inverseFabiusLogarithmicOrder_isLeast n hn).1, by
        rw [inverseFabiusLogarithmicDeltaDenominator_of_pos n hn]
        exact inv_inverseFabiusDeltaDenominator_le_fabiusReal F hF _⟩)

end Fabius
