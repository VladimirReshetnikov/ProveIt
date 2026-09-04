import FabiusFunction.FabiusInverseLogarithmicModulus
import Mathlib.Algebra.Order.Floor.Div

/-!
# Exact dyadic reciprocal moduli for the inverse Fabius function

The exact rational value `fabiusAtInverseTwoPow r` is the sharp input radius
for the inverse-output target `2⁻ʳ`.  Taking the natural ceiling of its
reciprocal therefore gives the least positive integer denominator whose
reciprocal is at most that radius.

This module proves both sides of the resulting sharp statement.  The ceiling
denominator supplies the strict inverse modulus, while the endpoint pair
`0, F(2⁻ʳ)` defeats every smaller positive denominator.  Composing with the
least logarithmic dyadic order gives a smaller witness for output tolerance
`1 / n` at positive `n`, with the harmless convention `d(0) = 1`.

The minimality theorem is deliberately restricted to the fixed dyadic target
`2⁻ʳ`.  The logarithmic corollary only gives the weaker target `1 / n` and
does not claim that its denominator is least for that weaker target.
-/

set_option autoImplicit false

open Set

namespace Fabius

private theorem fabiusAtInverseTwoPow_pos_exact (r : ℕ) :
    0 < fabiusAtInverseTwoPow r := by
  rw [fabiusAtInverseTwoPow_eq_recurrenceSequence]
  exact mul_pos (inv_pos.mpr (by positivity))
    (fabiusRecurrenceSequence_pos r)

private theorem inverseTwoPow_mem_Icc_exact (r : ℕ) :
    ((2 : ℝ) ^ r)⁻¹ ∈ Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))

/-! ## A primitive-recursive natural code for the exact endpoint mass -/

private theorem natFactorial_primrec_exact :
    Primrec Nat.factorial := by
  have hstep : Primrec₂ (fun n a : ℕ => (n + 1) * a) := by
    exact Primrec.nat_mul.comp₂
      (Primrec.succ.comp₂ Primrec₂.left) Primrec₂.right
  exact (Primrec.nat_rec₁ 1 hstep).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [Nat.factorial_succ, ih]

private theorem mersenneProduct_primrec_exact :
    Primrec mersenneProduct := by
  have hstep :
      Primrec₂ (fun n a : ℕ => a * (2 ^ (n + 1) - 1)) := by
    exact Primrec.nat_mul.comp₂ Primrec₂.right
      (Primrec.nat_sub.comp₂
        (primrec₂_nat_pow.comp₂ (Primrec.const 2).to₂
          (Primrec.succ.comp₂ Primrec₂.left))
        (Primrec.const 1).to₂)
  exact (Primrec.nat_rec₁ 1 hstep).of_eq fun n => by
    induction n with
    | zero => simp [mersenneProduct]
    | succ n ih => simp [mersenneProduct_succ_eq, ih]

private def natChooseExactCode (n k : ℕ) : ℕ :=
  if k ≤ n then n.factorial / (k.factorial * (n - k).factorial) else 0

private theorem natChooseExactCode_primrec :
    Primrec₂ natChooseExactCode := by
  apply Primrec₂.mk
  have hnfac : Primrec (fun p : ℕ × ℕ => p.1.factorial) :=
    natFactorial_primrec_exact.comp Primrec.fst
  have hkfac : Primrec (fun p : ℕ × ℕ => p.2.factorial) :=
    natFactorial_primrec_exact.comp Primrec.snd
  have hsubfac : Primrec (fun p : ℕ × ℕ => (p.1 - p.2).factorial) :=
    natFactorial_primrec_exact.comp
      (Primrec.nat_sub.comp Primrec.fst Primrec.snd)
  exact Primrec.ite
    (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (Primrec.nat_div.comp hnfac (Primrec.nat_mul.comp hkfac hsubfac))
    (Primrec.const 0)

private theorem natChoose_primrec_exact :
    Primrec₂ (fun n k : ℕ => Nat.choose n k) := by
  exact natChooseExactCode_primrec.of_eq fun n k => by
    by_cases hk : k ≤ n
    · simp [natChooseExactCode, hk,
        Nat.choose_eq_factorial_div_factorial hk]
    · have hnk : n < k := Nat.lt_of_not_ge hk
      simp [natChooseExactCode, hk, Nat.choose_eq_zero_of_lt hnk]

private def halfMomentCoefficientExactCode (n k : ℕ) : ℕ :=
  Nat.choose (n + 2) k *
    ((n + 1).factorial / (k + 1).factorial) *
    (mersenneProduct n / mersenneProduct k)

private theorem halfMomentCoefficientExactCode_primrec :
    Primrec₂ halfMomentCoefficientExactCode := by
  apply Primrec₂.mk
  have hn : Primrec (fun p : ℕ × ℕ => p.1) := Primrec.fst
  have hk : Primrec (fun p : ℕ × ℕ => p.2) := Primrec.snd
  have hnOne : Primrec (fun p : ℕ × ℕ => p.1 + 1) :=
    Primrec.succ.comp hn
  have hnTwo : Primrec (fun p : ℕ × ℕ => p.1 + 2) :=
    Primrec.succ.comp hnOne
  have hkOne : Primrec (fun p : ℕ × ℕ => p.2 + 1) :=
    Primrec.succ.comp hk
  have hchoose : Primrec (fun p : ℕ × ℕ => Nat.choose (p.1 + 2) p.2) :=
    natChoose_primrec_exact.comp hnTwo hk
  have hfactorialQuotient : Primrec
      (fun p : ℕ × ℕ => (p.1 + 1).factorial / (p.2 + 1).factorial) :=
    Primrec.nat_div.comp
      (natFactorial_primrec_exact.comp hnOne)
      (natFactorial_primrec_exact.comp hkOne)
  have hmersenneQuotient : Primrec
      (fun p : ℕ × ℕ => mersenneProduct p.1 / mersenneProduct p.2) :=
    Primrec.nat_div.comp
      (mersenneProduct_primrec_exact.comp hn)
      (mersenneProduct_primrec_exact.comp hk)
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp hchoose hfactorialQuotient)
    hmersenneQuotient

private theorem halfMomentCoefficientExactCode_eq
    (n k : ℕ) (hk : k ≤ n) :
    halfMomentCoefficientExactCode n k =
      Nat.choose (n + 2) k *
        (∏ j ∈ Finset.Ico (k + 2) (n + 2), j) *
        mersenneIntervalProduct (k + 1) (n + 1) := by
  have hfactorial := factorial_mul_interval n k hk
  have hmersenne := mersenneProduct_mul_interval n k hk
  rw [halfMomentCoefficientExactCode, ← hfactorial, ← hmersenne]
  simp [Nat.factorial_ne_zero, Nat.ne_of_gt (mersenneProduct_pos k)]

private theorem listSum_primrec_exact :
    Primrec (fun values : List ℕ => values.sum) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun values => by
        induction values <;> simp_all

private def halfMomentNumeratorSuccStepExactCode
    (values : List ℕ) (n : ℕ) : ℕ :=
  ((List.range values.length).map fun k =>
    values.getD k 0 * halfMomentCoefficientExactCode n k).sum

private theorem halfMomentNumeratorSuccStepExactCode_primrec :
    Primrec₂ halfMomentNumeratorSuccStepExactCode := by
  apply Primrec₂.mk
  have hrange : Primrec
      (fun p : List ℕ × ℕ => List.range p.1.length) :=
    Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)
  have hterm : Primrec₂
      (fun (p : List ℕ × ℕ) k =>
        p.1.getD k 0 * halfMomentCoefficientExactCode p.2 k) := by
    exact Primrec.nat_mul.comp₂
      (Primrec.list_getD 0 |>.comp₂
        (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
      (halfMomentCoefficientExactCode_primrec.comp₂
        (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
  exact listSum_primrec_exact.comp (Primrec.list_map hrange hterm)

private def halfMomentNumeratorStepExactCode (values : List ℕ) : ℕ :=
  values.length.casesOn 1 (halfMomentNumeratorSuccStepExactCode values)

private theorem halfMomentNumeratorStepExactCode_primrec :
    Primrec halfMomentNumeratorStepExactCode := by
  exact Primrec.nat_casesOn Primrec.list_length (Primrec.const 1)
    halfMomentNumeratorSuccStepExactCode_primrec

private theorem halfMomentNumeratorStepExactCode_spec (n : ℕ) :
    halfMomentNumeratorStepExactCode
        ((List.range n).map halfMomentNumerator) =
      halfMomentNumerator n := by
  cases n with
  | zero => simp [halfMomentNumeratorStepExactCode, halfMomentNumerator]
  | succ n =>
      simp only [halfMomentNumeratorStepExactCode, List.length_map,
        List.length_range]
      rw [halfMomentNumeratorSuccStepExactCode,
        List.length_map, List.length_range,
        ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
        halfMomentNumerator_succ]
      rw [Fin.sum_univ_eq_sum_range
        (fun k =>
          halfMomentNumerator k * Nat.choose (n + 2) k *
            (∏ j ∈ Finset.Ico (k + 2) (n + 2), j) *
            mersenneIntervalProduct (k + 1) (n + 1))
        (n + 1)]
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      have hkle : k ≤ n := by omega
      rw [halfMomentCoefficientExactCode_eq n k hkle]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hklt, mul_assoc]

private theorem halfMomentNumerator_primrec_exact :
    Primrec halfMomentNumerator := by
  have hgenerator : Primrec₂
      (fun (_ : Unit) (values : List ℕ) =>
        some (halfMomentNumeratorStepExactCode values)) := by
    exact Primrec.option_some.comp
      (halfMomentNumeratorStepExactCode_primrec.comp Primrec.snd)
  have hcourse : Primrec₂ (fun (_ : Unit) n => halfMomentNumerator n) := by
    refine Primrec.nat_strong_rec _ hgenerator ?_
    intro _ n
    rw [halfMomentNumeratorStepExactCode_spec]
  exact hcourse.comp (Primrec.const ()) Primrec.id

private def fabiusAtInverseTwoPowNaturalDenominator (r : ℕ) : ℕ :=
  2 ^ (r * (r - 1) / 2) * r.factorial * (r + 1).factorial *
    mersenneProduct r

private theorem fabiusAtInverseTwoPowNaturalDenominator_primrec :
    Primrec fabiusAtInverseTwoPowNaturalDenominator := by
  have htriangle : Primrec (fun r : ℕ => r * (r - 1) / 2) :=
    Primrec.nat_div.comp
      (Primrec.nat_mul.comp Primrec.id
        (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
      (Primrec.const 2)
  have hpow : Primrec (fun r : ℕ => 2 ^ (r * (r - 1) / 2)) :=
    primrec₂_nat_pow.comp (Primrec.const 2) htriangle
  have hfactorial : Primrec (fun r : ℕ => r.factorial) :=
    natFactorial_primrec_exact
  have hfactorialSucc : Primrec (fun r : ℕ => (r + 1).factorial) :=
    natFactorial_primrec_exact.comp Primrec.succ
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp hpow hfactorial) hfactorialSucc)
    mersenneProduct_primrec_exact

private theorem fabiusAtInverseTwoPow_eq_naturalQuotient (r : ℕ) :
    fabiusAtInverseTwoPow r =
      (halfMomentNumerator r : ℚ) /
        (fabiusAtInverseTwoPowNaturalDenominator r : ℚ) := by
  rw [fabiusAtInverseTwoPow_eq_halfMomentNumerator_formula,
    fabiusAtInverseTwoPowNaturalDenominator, Nat.choose_two_right]
  push_cast
  rfl

private theorem halfMomentNumerator_pos_exact (r : ℕ) :
    0 < halfMomentNumerator r := by
  have hmass := fabiusAtInverseTwoPow_pos_exact r
  rw [fabiusAtInverseTwoPow_eq_naturalQuotient] at hmass
  apply Nat.pos_of_ne_zero
  intro hzero
  rw [hzero] at hmass
  norm_num at hmass

private def natCeilQuotientExactCode (a b : ℕ) : ℕ :=
  (a + b - 1) / b

private theorem natCeilQuotientExactCode_primrec :
    Primrec₂ natCeilQuotientExactCode := by
  apply Primrec₂.mk
  exact Primrec.nat_div.comp
    (Primrec.nat_sub.comp
      (Primrec.nat_add.comp Primrec.fst Primrec.snd)
      (Primrec.const 1))
    Primrec.snd

private theorem natCeil_ratQuotient_eq_exactCode
    (a b : ℕ) (hb : 0 < b) :
    ⌈(a : ℚ) / (b : ℚ)⌉₊ = natCeilQuotientExactCode a b := by
  rw [natCeilQuotientExactCode, ← Nat.ceilDiv_eq_add_pred_div]
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hb)]
    have hbound : a ≤ b * (a ⌈/⌉ b) :=
      (ceilDiv_le_iff_le_mul hb).mp le_rfl
    have hbound' : a ≤ (a ⌈/⌉ b) * b := by
      simpa [Nat.mul_comm] using hbound
    exact_mod_cast hbound'
  · rw [ceilDiv_le_iff_le_mul hb]
    have hceil := Nat.le_ceil ((a : ℚ) / (b : ℚ))
    rw [div_le_iff₀ (by exact_mod_cast hb)] at hceil
    rw [mul_comm] at hceil
    exact_mod_cast hceil

/-! ## The least denominator at a fixed dyadic target -/

/-- The least positive natural denominator whose reciprocal is at most the
exact endpoint mass `F(2⁻ʳ)`.

The definition uses the exact rational evaluator, so no ceiling of an
approximated real number is involved. -/
def inverseFabiusExactDyadicDenominator (r : ℕ) : ℕ :=
  ⌈(fabiusAtInverseTwoPow r)⁻¹⌉₊

private theorem inverseFabiusExactDyadicDenominator_eq_naturalCode
    (r : ℕ) :
    inverseFabiusExactDyadicDenominator r =
      natCeilQuotientExactCode
        (fabiusAtInverseTwoPowNaturalDenominator r)
        (halfMomentNumerator r) := by
  rw [inverseFabiusExactDyadicDenominator,
    fabiusAtInverseTwoPow_eq_naturalQuotient, inv_div]
  exact natCeil_ratQuotient_eq_exactCode _ _
    (halfMomentNumerator_pos_exact r)

/-- The least exact dyadic denominator is primitive recursive.  The proof
uses a natural numerator/denominator code for the exact rational endpoint
mass, so it does not require a computability API for normalized rationals. -/
theorem inverseFabiusExactDyadicDenominator_primrec :
    Primrec inverseFabiusExactDyadicDenominator := by
  have hcode : Primrec (fun r =>
      natCeilQuotientExactCode
        (fabiusAtInverseTwoPowNaturalDenominator r)
        (halfMomentNumerator r)) :=
    natCeilQuotientExactCode_primrec.comp
      fabiusAtInverseTwoPowNaturalDenominator_primrec
      halfMomentNumerator_primrec_exact
  exact hcode.of_eq fun r =>
    (inverseFabiusExactDyadicDenominator_eq_naturalCode r).symm

/-- The exact dyadic denominator is strictly positive at every order,
including order zero. -/
theorem inverseFabiusExactDyadicDenominator_pos (r : ℕ) :
    0 < inverseFabiusExactDyadicDenominator r := by
  rw [inverseFabiusExactDyadicDenominator, Nat.ceil_pos]
  exact inv_pos.mpr (fabiusAtInverseTwoPow_pos_exact r)

/-- The reciprocal of the exact dyadic denominator lies below the exact
rational endpoint mass. -/
theorem inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow
    (r : ℕ) :
    ((inverseFabiusExactDyadicDenominator r : ℚ))⁻¹ ≤
      fabiusAtInverseTwoPow r := by
  have hmass : 0 < fabiusAtInverseTwoPow r :=
    fabiusAtInverseTwoPow_pos_exact r
  have hden : (0 : ℚ) < inverseFabiusExactDyadicDenominator r := by
    exact_mod_cast inverseFabiusExactDyadicDenominator_pos r
  apply (inv_le_comm₀ hmass hden).1
  exact Nat.le_ceil _

/-- The ceiling denominator is the least positive natural denominator whose
reciprocal is bounded by the exact rational endpoint mass. -/
theorem inverseFabiusExactDyadicDenominator_isLeast (r : ℕ) :
    IsLeast
      {d : ℕ | 0 < d ∧ ((d : ℚ))⁻¹ ≤ fabiusAtInverseTwoPow r}
      (inverseFabiusExactDyadicDenominator r) := by
  constructor
  · exact ⟨inverseFabiusExactDyadicDenominator_pos r,
      inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow r⟩
  · intro d hd
    rw [inverseFabiusExactDyadicDenominator, Nat.ceil_le]
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd.1
    exact (inv_le_comm₀ hdq (fabiusAtInverseTwoPow_pos_exact r)).1 hd.2

/-! ## Sharp strict inverse moduli -/

/-- The exact ceiling denominator gives the strict inverse modulus for the
fixed dyadic output target `2⁻ʳ`. -/
theorem abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) {u v : ℝ}
    (huv : |u - v| <
      ((inverseFabiusExactDyadicDenominator r : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < ((2 : ℝ) ^ r)⁻¹ := by
  have hthresholdQ :=
    inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow r
  have hthresholdR := Rat.cast_mono (K := ℝ) hthresholdQ
  push_cast at hthresholdR
  rw [fabiusAtInverseTwoPow_cast F hF r] at hthresholdR
  exact abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal F hF
    (inverseTwoPow_mem_Icc_exact r) (huv.trans_le hthresholdR)

/-- Every smaller positive denominator fails at the endpoint pair
`0, F(2⁻ʳ)`: its input gap is below the proposed reciprocal radius, while its
inverse-output gap is exactly `2⁻ʳ`. -/
theorem exists_fabiusInv_gap_of_lt_exactDyadicDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r d : ℕ)
    (hdpos : 0 < d) (hd : d < inverseFabiusExactDyadicDenominator r) :
    ∃ u v : ℝ,
      |u - v| < ((d : ℝ))⁻¹ ∧
      |fabiusInv F hF u - fabiusInv F hF v| = ((2 : ℝ) ^ r)⁻¹ := by
  have hmass : 0 < fabiusAtInverseTwoPow r :=
    fabiusAtInverseTwoPow_pos_exact r
  have hdq : (0 : ℚ) < d := by exact_mod_cast hdpos
  have hdlt : (d : ℚ) < (fabiusAtInverseTwoPow r)⁻¹ := by
    exact (Nat.lt_ceil.mp (by
      simpa only [inverseFabiusExactDyadicDenominator] using hd))
  have hmassltQ : fabiusAtInverseTwoPow r < ((d : ℚ))⁻¹ :=
    (lt_inv_comm₀ hmass hdq).2 hdlt
  have hmassltR := (Rat.cast_lt (K := ℝ)).2 hmassltQ
  push_cast at hmassltR
  rw [fabiusAtInverseTwoPow_cast F hF r] at hmassltR
  refine ⟨0, fabiusReal F (((2 : ℝ) ^ r)⁻¹), ?_, ?_⟩
  · simpa [abs_of_nonneg (fabiusReal_nonneg F (((2 : ℝ) ^ r)⁻¹))] using
      hmassltR
  · rw [fabiusInv_zero F hF,
      fabiusInv_fabiusReal F hF (inverseTwoPow_mem_Icc_exact r),
      zero_sub, abs_neg, abs_of_nonneg (inverseTwoPow_mem_Icc_exact r).1]

/-- The exact ceiling denominator is the least positive integer strict
modulus for the fixed dyadic output target.  This is a target-specific
optimality statement, not optimality for a larger output tolerance. -/
theorem inverseFabiusExactDyadicDenominator_isLeast_strictModulus
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    IsLeast
      {d : ℕ | 0 < d ∧
        ∀ u v : ℝ, |u - v| < ((d : ℝ))⁻¹ →
          |fabiusInv F hF u - fabiusInv F hF v| < ((2 : ℝ) ^ r)⁻¹}
      (inverseFabiusExactDyadicDenominator r) := by
  constructor
  · exact ⟨inverseFabiusExactDyadicDenominator_pos r,
      fun _u _v huv =>
        abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator
          F hF r huv⟩
  · intro d hd
    by_contra hnot
    have hlt : d < inverseFabiusExactDyadicDenominator r :=
      Nat.lt_of_not_ge hnot
    rcases exists_fabiusInv_gap_of_lt_exactDyadicDenominator
      F hF r d hd.1 hlt with ⟨u, v, huv, hgap⟩
    have hstrict := hd.2 u v huv
    rw [hgap] at hstrict
    exact (lt_irrefl _) hstrict

/-! ## A logarithmic witness for reciprocal output tolerances -/

/-- The exact dyadic denominator evaluated at the least order whose dyadic
scale is strictly below `1 / n`.  Its value at zero is defined to be `1`;
no modulus conclusion is asserted at that convention-only input. -/
def inverseFabiusExactLogarithmicDenominator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      inverseFabiusExactDyadicDenominator
        (inverseFabiusLogarithmicOrder (n + 1))

/-- The exact logarithmic denominator, including its convention-only value
at zero, is primitive recursive. -/
theorem inverseFabiusExactLogarithmicDenominator_primrec :
    Primrec inverseFabiusExactLogarithmicDenominator := by
  exact (Primrec.nat_casesOn₁ 1
    (inverseFabiusExactDyadicDenominator_primrec.comp
      (inverseFabiusLogarithmicOrder_primrec.comp Primrec.succ))).of_eq
        fun n => by cases n <;> rfl

/-- At positive inputs the logarithmic denominator is exactly the fixed-target
ceiling denominator at the least logarithmic dyadic order. -/
theorem inverseFabiusExactLogarithmicDenominator_of_pos
    (n : ℕ) (hn : 0 < n) :
    inverseFabiusExactLogarithmicDenominator n =
      inverseFabiusExactDyadicDenominator
        (inverseFabiusLogarithmicOrder n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rfl

/-- At every positive `n`, the exact logarithmic denominator gives output
error below `1 / n`.  Its leastness is only for the stronger fixed dyadic
target `2⁻ʳ⁽ⁿ⁾`; no least-denominator claim is made here for `1 / n`. -/
theorem abs_fabiusInv_sub_lt_inv_nat_of_lt_exactLogarithmicDenominator
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n)
    {u v : ℝ}
    (huv : |u - v| <
      ((inverseFabiusExactLogarithmicDenominator n : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < (n : ℝ)⁻¹ := by
  have huv' : |u - v| <
      ((inverseFabiusExactDyadicDenominator
        (inverseFabiusLogarithmicOrder n) : ℝ))⁻¹ := by
    rw [← inverseFabiusExactLogarithmicDenominator_of_pos n hn]
    exact huv
  have hdyadic :=
    abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator
      F hF (inverseFabiusLogarithmicOrder n) huv'
  have hpowNat := (inverseFabiusLogarithmicOrder_isLeast n hn).1
  have hpowReal : (n : ℝ) <
      (2 : ℝ) ^ inverseFabiusLogarithmicOrder n := by
    exact_mod_cast hpowNat
  have hinv :
      ((2 : ℝ) ^ inverseFabiusLogarithmicOrder n)⁻¹ < (n : ℝ)⁻¹ :=
    (inv_lt_inv₀ (by positivity) (by exact_mod_cast hn)).2 hpowReal
  exact hdyadic.trans hinv

end Fabius
