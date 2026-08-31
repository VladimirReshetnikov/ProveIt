import FabiusFunction.CompleteHomogeneousGenerating
import FabiusFunction.ReciprocalExponentialGenerating

/-!
# Complete homogeneous functions as complete Bell polynomials

For a finite family `a`, write `p k = ∑ i in s, a i ^ k`.  The classical
power-sum formula for complete homogeneous symmetric polynomials is

`Bell.complete (fun k => (k - 1)! * p k) n = n! * h_n(a)`.

This module proves that identity first over an arbitrary commutative semiring.
The input at zero is fixed to zero and the positive input of index `k + 1` is
`k! * p_(k+1)`, so neither subtraction nor division occurs.  Repeated values,
nilpotents, zero divisors, positive characteristic, and the zero ring are all
allowed.

Over a commutative `ℚ`-algebra, the existing dictionary between
`Bell.complete` and `completeBellPolynomial` then gives the familiar report
form

`h_n(a) = B_n(0! p_1, 1! p_2, ..., (n-1)! p_n) / n!`,

with division represented by `factorialNormalize`.

## Main results

* `completeHomogeneousPowerSum` is the finite power-sum sequence.
* `completeHomogeneousBellInput` is the factorially weighted Bell input.
* `bellComplete_completeHomogeneousBellInput` is the division-free identity
  over every commutative semiring.
* `factorialNormalize_completeBellPolynomial_completeHomogeneousBellInput`
  is the sequence-valued `ℚ`-algebra form.
* `completeHomogeneousEvalOn_eq_factorialNormalize_completeBellPolynomial`
  is its pointwise report form.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-- The `k`th power sum of the finite family `a` indexed by `s`. -/
def completeHomogeneousPowerSum
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (k : ℕ) : R :=
  ∑ i ∈ s, a i ^ k

/-- The factorially weighted power sums used as complete-Bell inputs.

The value at zero is immaterial to `Bell.complete` and is normalized to zero;
at the positive index `k + 1` the value is `k! * p_(k+1)`. -/
def completeHomogeneousBellInput
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) : ℕ → R
  | 0 => 0
  | k + 1 => (k.factorial : R) * completeHomogeneousPowerSum s a (k + 1)

/-- Adjoining one variable expands a complete homogeneous evaluation as its
finite geometric convolution with the old family. -/
theorem completeHomogeneousEvalOn_insert_eq_sum
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (a : ι → R) (n : ℕ) :
    completeHomogeneousEvalOn (insert i s) a n =
      ∑ k ∈ Finset.range (n + 1),
        a i ^ (n - k) * completeHomogeneousEvalOn s a k := by
  induction n with
  | zero =>
      simp [completeHomogeneousEvalOn]
  | succ n ih =>
      rw [completeHomogeneousEvalOn_insert_succ hi a n, ih]
      calc
        a i *
              (∑ k ∈ Finset.range (n + 1),
                a i ^ (n - k) * completeHomogeneousEvalOn s a k) +
            completeHomogeneousEvalOn s a (n + 1) =
            (∑ k ∈ Finset.range (n + 1),
                a i ^ (n + 1 - k) *
                  completeHomogeneousEvalOn s a k) +
              completeHomogeneousEvalOn s a (n + 1) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k ≤ n :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
          ac_rfl
        _ = ∑ k ∈ Finset.range (n + 2),
              a i ^ (n + 1 - k) *
                completeHomogeneousEvalOn s a k := by
          symm
          rw [Finset.sum_range_succ]
          simp

private def singlePowerBellInput
    {R : Type*} [CommSemiring R] (x : R) : ℕ → R
  | 0 => 0
  | k + 1 => (k.factorial : R) * x ^ (k + 1)

private theorem cast_choose_mul_factorials
    {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : R) * (k.factorial : R) * ((n - k).factorial : R) =
      (n.factorial : R) := by
  simpa only [Nat.cast_mul] using
    congrArg (fun m : ℕ => (m : R))
      (Nat.choose_mul_factorial_mul_factorial hk)

private theorem bellComplete_singlePowerBellInput
    {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    Bell.complete (singlePowerBellInput x) n =
      (n.factorial : R) * x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [Bell.complete]
          calc
            (∑ j ∈ Finset.range (n + 1),
                (n.choose j : R) *
                  (singlePowerBellInput x (j + 1) *
                    Bell.complete (singlePowerBellInput x) (n - j))) =
                ∑ _j ∈ Finset.range (n + 1),
                  (n.factorial : R) * x ^ (n + 1) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hj' : j ≤ n :=
                Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              rw [ih (n - j) (by omega)]
              simp only [singlePowerBellInput]
              have hfac := cast_choose_mul_factorials (R := R) n j hj'
              have hpow : j + 1 + (n - j) = n + 1 := by omega
              have hxpow : x ^ (j + 1) * x ^ (n - j) = x ^ (n + 1) := by
                rw [← pow_add, hpow]
              calc
                _ =
                    ((n.choose j : R) * (j.factorial : R) *
                      ((n - j).factorial : R)) *
                        (x ^ (j + 1) * x ^ (n - j)) := by ring
                _ = ((n.choose j : R) * (j.factorial : R) *
                      ((n - j).factorial : R)) * x ^ (n + 1) := by
                        rw [hxpow]
                _ = (n.factorial : R) * x ^ (n + 1) := by rw [hfac]
            _ = ((n + 1).factorial : R) * x ^ (n + 1) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                Nat.factorial_succ, Nat.cast_mul]
              ring

private theorem completeHomogeneousBellInput_insert
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (a : ι → R) :
    completeHomogeneousBellInput (insert i s) a =
      completeHomogeneousBellInput s a + singlePowerBellInput (a i) := by
  funext n
  cases n with
  | zero => simp [completeHomogeneousBellInput, singlePowerBellInput]
  | succ n =>
      simp [completeHomogeneousBellInput, completeHomogeneousPowerSum,
        singlePowerBellInput, Finset.sum_insert, hi, mul_add, add_comm]

/-- **Complete homogeneous--Bell identity, division-free form.**

For every finite family over a commutative semiring, the complete Bell family
of the factorially weighted power sums is exactly `n!` times the degree-`n`
complete homogeneous evaluation. -/
theorem bellComplete_completeHomogeneousBellInput
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (n : ℕ) :
    Bell.complete (completeHomogeneousBellInput s a) n =
      (n.factorial : R) * completeHomogeneousEvalOn s a n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      have hinput :
          completeHomogeneousBellInput (∅ : Finset ι) a = 0 := by
        funext k
        cases k <;>
          simp [completeHomogeneousBellInput, completeHomogeneousPowerSum]
      rw [hinput, Bell.complete_zero_eq_unitSeq]
      cases n with
      | zero => simp [completeHomogeneousEvalOn]
      | succ n => simp [Bell.unitSeq, completeHomogeneousEvalOn]
  | @insert i s hi ih =>
      rw [completeHomogeneousBellInput_insert hi a, Bell.complete_add,
        Bell.binomialConv_eq_sum_range]
      calc
        (∑ k ∈ Finset.range (n + 1),
            (n.choose k : R) *
              (Bell.complete (completeHomogeneousBellInput s a) k *
                Bell.complete (singlePowerBellInput (a i)) (n - k))) =
            ∑ k ∈ Finset.range (n + 1),
              (n.factorial : R) *
                (a i ^ (n - k) * completeHomogeneousEvalOn s a k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k ≤ n :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [ih k, bellComplete_singlePowerBellInput]
          have hfac := cast_choose_mul_factorials (R := R) n k hk'
          calc
            _ =
                ((n.choose k : R) * (k.factorial : R) *
                  ((n - k).factorial : R)) *
                    (a i ^ (n - k) * completeHomogeneousEvalOn s a k) := by
                      ring
            _ = (n.factorial : R) *
                (a i ^ (n - k) * completeHomogeneousEvalOn s a k) := by
                  rw [hfac]
        _ = (n.factorial : R) *
            (∑ k ∈ Finset.range (n + 1),
              a i ^ (n - k) * completeHomogeneousEvalOn s a k) := by
                rw [Finset.mul_sum]
        _ = (n.factorial : R) *
            completeHomogeneousEvalOn (insert i s) a n := by
              rw [completeHomogeneousEvalOn_insert_eq_sum hi a n]

section RationalAlgebra

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The sequence-valued report form: factorial normalization of the complete
Bell polynomials of the weighted power sums is the complete homogeneous
sequence. -/
theorem factorialNormalize_completeBellPolynomial_completeHomogeneousBellInput
    {ι : Type*} (s : Finset ι) (a : ι → R) :
    factorialNormalize
        (completeBellPolynomial (completeHomogeneousBellInput s a)) =
      fun n ↦ completeHomogeneousEvalOn s a n := by
  let h : ℕ → R := fun n ↦ completeHomogeneousEvalOn s a n
  have hcomplete :
      Bell.complete (completeHomogeneousBellInput s a) =
        factorialDenormalize h := by
    funext n
    rw [bellComplete_completeHomogeneousBellInput]
    simp [h, factorialDenormalize, Algebra.smul_def]
  calc
    factorialNormalize
        (completeBellPolynomial (completeHomogeneousBellInput s a)) =
        factorialNormalize
          (Bell.complete (completeHomogeneousBellInput s a)) := by
            rw [completeBellPolynomial_eq_complete]
    _ = factorialNormalize (factorialDenormalize h) := by rw [hcomplete]
    _ = h := factorialNormalize_factorialDenormalize h
    _ = fun n ↦ completeHomogeneousEvalOn s a n := rfl

/-- The pointwise report identity

`h_n(a) = B_n(0! p_1, 1! p_2, ..., (n-1)! p_n) / n!`,

where division by `n!` is expressed by `factorialNormalize`. -/
theorem completeHomogeneousEvalOn_eq_factorialNormalize_completeBellPolynomial
    {ι : Type*} (s : Finset ι) (a : ι → R) (n : ℕ) :
    completeHomogeneousEvalOn s a n =
      factorialNormalize
        (completeBellPolynomial (completeHomogeneousBellInput s a)) n := by
  exact (congrFun
    (factorialNormalize_completeBellPolynomial_completeHomogeneousBellInput
      s a) n).symm

end RationalAlgebra

end

end Fabius
