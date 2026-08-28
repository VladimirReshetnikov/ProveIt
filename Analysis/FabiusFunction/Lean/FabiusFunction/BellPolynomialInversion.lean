import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Division-free Bell-polynomial inversion

This module develops the coefficient algebra of exponential generating
functions without division.  For sequences `a b : ℕ → R`, their binomial
convolution is

`(a ⋆ b) n = ∑ k ≤ n, (n.choose k) · a k · b (n-k)`.

Over a semiring this operation has a product rule under the shift
`a ↦ (n ↦ a (n+1))` and is associative.  It admits cancellation when the
zeroth coefficient of the fixed factor is a unit and addition in the
coefficient semiring is left-cancellative.  Over a commutative semiring the
complete Bell family `complete κ` is the unique solution of

`B 0 = 1`,  `B (n+1) = (B ⋆ shift κ) n`.

Over a commutative ring the recurrence can be inverted without factorials or
division.  The resulting `cumulant m` satisfies

`complete (cumulant m) = m`

whenever `m 0 = 1`, and a normalized cumulant sequence is recovered uniquely
from its complete Bell family.  Thus the familiar moment--cumulant inversion
lives over every commutative ring, including positive characteristic and the
zero ring.

The associativity proof is deliberately structural.  Pascal's identity gives
the shift product rule, and induction on the coefficient index reduces
associativity to that rule.  This avoids a bespoke reindexing of a triangular
triple sum and makes the exponential-series mechanism visible in the proof.

## Main results

* `Bell.binomialConv_assoc`, `Bell.binomialConv_comm`, and
  `Bell.binomialConv_right_cancel` give the reusable convolution algebra.
* `Bell.complete_succ`, `Bell.eq_complete_of_recurrence`, and
  `Bell.complete_add` characterize the complete Bell transform and prove its
  exponential addition law.
* `Bell.complete_cumulant` and `Bell.eq_cumulant_of_complete` are the two
  directions of division-free moment--cumulant inversion.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Bell

/-! ## Sequences, shifts, and binomial convolution -/

/-- The left shift of a sequence: `(shift a) n = a (n+1)`. -/
def shift {R : Type*} (a : ℕ → R) (n : ℕ) : R := a (n + 1)

/-- Evaluation of the left shift. -/
@[simp]
theorem shift_apply {R : Type*} (a : ℕ → R) (n : ℕ) : shift a n = a (n + 1) := rfl

/-- The coefficient sequence of the constant exponential series `1`. -/
def unitSeq (R : Type*) [Zero R] [One R] : ℕ → R
  | 0 => 1
  | _ + 1 => 0

/-- The zeroth coefficient of the unit sequence is one. -/
@[simp]
theorem unitSeq_zero (R : Type*) [Zero R] [One R] : unitSeq R 0 = 1 := rfl

/-- Every positive coefficient of the unit sequence is zero. -/
@[simp]
theorem unitSeq_succ (R : Type*) [Zero R] [One R] (n : ℕ) : unitSeq R (n + 1) = 0 := rfl

section Semiring

variable {R : Type*} [Semiring R]

/-- The binomial convolution of two sequences, i.e. multiplication of their
exponential generating functions read directly on coefficients. -/
def binomialConv (a b : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * (a k * b (n - k))

/-- The defining finite-sum formula for binomial convolution. -/
theorem binomialConv_eq_sum_range (a b : ℕ → R) (n : ℕ) :
    binomialConv a b n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * (a k * b (n - k)) := rfl

/-- Binomial convolution distributes over addition in its left argument. -/
theorem binomialConv_add_left (a b c : ℕ → R) :
    binomialConv (a + b) c = binomialConv a c + binomialConv b c := by
  funext n
  simp only [binomialConv, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

/-- Binomial convolution distributes over addition in its right argument. -/
theorem binomialConv_add_right (a b c : ℕ → R) :
    binomialConv a (b + c) = binomialConv a b + binomialConv a c := by
  funext n
  simp only [binomialConv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Pascal's identity as the product rule for binomial convolution:
`(a ⋆ b)_(n+1) = (a ⋆ shift b)_n + (shift a ⋆ b)_n`. -/
theorem binomialConv_succ (a b : ℕ → R) (n : ℕ) :
    binomialConv a b (n + 1) =
      binomialConv a (shift b) n + binomialConv (shift a) b n := by
  change (∑ i ∈ Finset.range (n + 2),
      ((n + 1).choose i : R) * (a i * b (n + 1 - i))) = _
  rw [Finset.sum_choose_succ_mul (fun i j => a i * b j) n,
    binomialConv_eq_sum_range, binomialConv_eq_sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [shift_apply]
    rw [show n + 1 - i = n - i + 1 by omega]

/-- Shifting a convolution differentiates its two factors, in the formal
exponential-generating-function sense. -/
theorem shift_binomialConv (a b : ℕ → R) :
    shift (binomialConv a b) =
      binomialConv a (shift b) + binomialConv (shift a) b := by
  funext n
  simpa only [shift_apply, Pi.add_apply] using binomialConv_succ a b n

/-- Binomial convolution is associative over every semiring. -/
theorem binomialConv_assoc (a b c : ℕ → R) :
    binomialConv (binomialConv a b) c = binomialConv a (binomialConv b c) := by
  funext n
  induction n generalizing a b c with
  | zero => simp [binomialConv, mul_assoc]
  | succ n ih =>
    calc
      binomialConv (binomialConv a b) c (n + 1)
          = binomialConv (binomialConv a b) (shift c) n +
              binomialConv (shift (binomialConv a b)) c n :=
            binomialConv_succ _ _ n
      _ = binomialConv (binomialConv a b) (shift c) n +
              binomialConv
                (binomialConv a (shift b) + binomialConv (shift a) b) c n := by
            rw [shift_binomialConv]
      _ = binomialConv (binomialConv a b) (shift c) n +
              (binomialConv (binomialConv a (shift b)) c n +
                binomialConv (binomialConv (shift a) b) c n) := by
            rw [congrFun (binomialConv_add_left _ _ _) n, Pi.add_apply]
      _ = binomialConv a (binomialConv b (shift c)) n +
              (binomialConv a (binomialConv (shift b) c) n +
                binomialConv (shift a) (binomialConv b c) n) := by
            rw [ih, ih, ih]
      _ = binomialConv a
              (binomialConv b (shift c) + binomialConv (shift b) c) n +
              binomialConv (shift a) (binomialConv b c) n := by
            rw [congrFun (binomialConv_add_right _ _ _) n, Pi.add_apply]
            ac_rfl
      _ = binomialConv a (shift (binomialConv b c)) n +
              binomialConv (shift a) (binomialConv b c) n := by
            rw [shift_binomialConv]
      _ = binomialConv a (binomialConv b c) (n + 1) :=
            (binomialConv_succ _ _ n).symm

/-- Right cancellation for binomial convolution when the fixed sequence has a
unit zeroth coefficient and the coefficient semiring has left-cancellative
addition.  Higher coefficients are recovered triangularly. -/
theorem binomialConv_right_cancel [IsLeftCancelAdd R] {a b w : ℕ → R}
    (hw : IsUnit (w 0))
    (h : ∀ n, binomialConv a w n = binomialConv b w n) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := h n
    rw [binomialConv_eq_sum_range, binomialConv_eq_sum_range,
      Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hp :
        (∑ k ∈ Finset.range n, (n.choose k : R) * (a k * w (n - k))) =
          ∑ k ∈ Finset.range n, (n.choose k : R) * (b k * w (n - k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ih k (Finset.mem_range.mp hk)]
    rw [hp] at hn
    apply hw.mul_right_cancel
    simpa using (add_left_cancel hn)

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Binomial convolution is commutative over a commutative semiring. -/
theorem binomialConv_comm (a b : ℕ → R) : binomialConv a b = binomialConv b a := by
  funext n
  rw [binomialConv_eq_sum_range, binomialConv_eq_sum_range,
    ← Finset.sum_range_reflect
      (fun k => (n.choose k : R) * (b k * a (n - k))) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hk', Nat.sub_sub_self hk']
  ring

/-! ## Complete Bell families -/

/-- The complete exponential Bell family, defined by its division-free
successor recurrence.  The supplied value `κ 0` is irrelevant. -/
def complete (κ : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 =>
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : R) * (κ (j + 1) * complete κ (n - j))
termination_by n => n
decreasing_by omega

/-- The zeroth complete Bell polynomial is one. -/
@[simp]
theorem complete_zero (κ : ℕ → R) : complete κ 0 = 1 := by
  rw [complete]

/-- The complete Bell family obeys `B_(n+1) = (B ⋆ shift κ)_n`. -/
theorem complete_succ (κ : ℕ → R) (n : ℕ) :
    complete κ (n + 1) = binomialConv (complete κ) (shift κ) n := by
  rw [complete]
  change binomialConv (shift κ) (complete κ) n = _
  exact congrFun (binomialConv_comm (shift κ) (complete κ)) n

/-- The complete Bell family is the unique normalized solution of its
successor recurrence. -/
theorem eq_complete_of_recurrence (κ a : ℕ → R) (h0 : a 0 = 1)
    (hs : ∀ n, a (n + 1) = binomialConv a (shift κ) n) : a = complete κ := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      rw [hs n, complete_succ, binomialConv_eq_sum_range,
        binomialConv_eq_sum_range]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ih k (Finset.mem_range.mp hk)]

/-- The shift of a complete Bell family is its convolution with the shifted
cumulant sequence. -/
theorem shift_complete (κ : ℕ → R) :
    shift (complete κ) = binomialConv (complete κ) (shift κ) := by
  funext n
  exact complete_succ κ n

/-- The exponential addition law for complete Bell families:
`complete (κ + μ) = complete κ ⋆ complete μ`. -/
theorem complete_add (κ μ : ℕ → R) :
    complete (κ + μ) = binomialConv (complete κ) (complete μ) := by
  symm
  refine eq_complete_of_recurrence (κ + μ) _ ?_ ?_
  · simp [binomialConv]
  · intro n
    rw [binomialConv_succ, shift_complete, shift_complete]
    calc
      binomialConv (complete κ) (binomialConv (complete μ) (shift μ)) n +
          binomialConv (binomialConv (complete κ) (shift κ)) (complete μ) n
        = binomialConv (binomialConv (complete κ) (complete μ)) (shift μ) n +
            binomialConv (binomialConv (complete κ) (complete μ)) (shift κ) n := by
              rw [← binomialConv_assoc,
                binomialConv_assoc (complete κ) (shift κ) (complete μ),
                binomialConv_comm (shift κ) (complete μ), ← binomialConv_assoc]
      _ = binomialConv (binomialConv (complete κ) (complete μ))
          (shift κ + shift μ) n := by
            rw [congrFun (binomialConv_add_right
              (binomialConv (complete κ) (complete μ)) (shift κ) (shift μ)) n,
              Pi.add_apply]
            ac_rfl
      _ = binomialConv (binomialConv (complete κ) (complete μ))
          (shift (κ + μ)) n := by
            have hs : shift (κ + μ) = shift κ + shift μ := by rfl
            rw [hs]

/-- The first complete Bell polynomial is `κ₁`. -/
@[simp]
theorem complete_one (κ : ℕ → R) : complete κ 1 = κ 1 := by
  norm_num [complete]

/-- The second complete Bell polynomial is `κ₁² + κ₂`. -/
theorem complete_two (κ : ℕ → R) : complete κ 2 = κ 1 ^ 2 + κ 2 := by
  norm_num [complete, Finset.sum_range_succ]
  ring

/-- The third complete Bell polynomial is `κ₁³ + 3κ₁κ₂ + κ₃`. -/
theorem complete_three (κ : ℕ → R) :
    complete κ 3 = κ 1 ^ 3 + 3 * κ 1 * κ 2 + κ 3 := by
  norm_num [complete, Finset.sum_range_succ]
  ring

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-! ## Division-free cumulants and inversion -/

/-- The cumulant sequence of `m`, obtained by solving the complete-Bell
recurrence triangularly.  Its zeroth value is normalized to zero. -/
def cumulant (m : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 =>
      m (n + 1) - ∑ j ∈ Finset.range n,
        (n.choose (j + 1) : R) * (m (j + 1) * cumulant m (n - j))
termination_by n => n
decreasing_by omega

/-- The zeroth cumulant is zero. -/
@[simp]
theorem cumulant_zero (m : ℕ → R) : cumulant m 0 = 0 := by
  rw [cumulant]

/-- The explicit triangular successor recurrence for cumulants. -/
theorem cumulant_succ (m : ℕ → R) (n : ℕ) :
    cumulant m (n + 1) =
      m (n + 1) - ∑ j ∈ Finset.range n,
        (n.choose (j + 1) : R) * (m (j + 1) * cumulant m (n - j)) := by
  rw [cumulant]

private theorem binomialConv_shift_eq_tail_add (m κ : ℕ → R) (n : ℕ) :
    binomialConv m (shift κ) n =
      (∑ j ∈ Finset.range n,
        (n.choose (j + 1) : R) * (m (j + 1) * κ (n - j))) +
        m 0 * κ (n + 1) := by
  rw [binomialConv_eq_sum_range, Finset.sum_range_succ']
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.mp hj
    simp only [shift_apply]
    rw [show n - (j + 1) + 1 = n - j by omega]
  · simp [shift]

/-- A normalized sequence convolved with the shift of its cumulants reproduces
its own shifted coefficients. -/
theorem binomialConv_cumulant_shift (m : ℕ → R) (h0 : m 0 = 1) (n : ℕ) :
    binomialConv m (shift (cumulant m)) n = m (n + 1) := by
  rw [binomialConv_shift_eq_tail_add, h0, one_mul, cumulant_succ]
  ring

/-- Complete Bell polynomials of the cumulants of a normalized sequence
recover that sequence. -/
theorem complete_cumulant (m : ℕ → R) (h0 : m 0 = 1) :
    complete (cumulant m) = m := by
  symm
  refine eq_complete_of_recurrence (cumulant m) m h0 fun n => ?_
  exact (binomialConv_cumulant_shift m h0 n).symm

private theorem eq_cumulant_of_recurrence {m κ : ℕ → R}
    (hm0 : m 0 = 1) (hκ0 : κ 0 = 0)
    (hrec : ∀ n, m (n + 1) = binomialConv m (shift κ) n) :
    κ = cumulant m := by
  funext N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero => simpa using hκ0
    | succ n =>
      rw [cumulant_succ]
      have hn := hrec n
      rw [binomialConv_shift_eq_tail_add, hm0, one_mul] at hn
      have hs :
          (∑ j ∈ Finset.range n,
            (n.choose (j + 1) : R) * (m (j + 1) * κ (n - j))) =
            ∑ j ∈ Finset.range n,
              (n.choose (j + 1) : R) *
                (m (j + 1) * cumulant m (n - j)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [ih (n - j) (by omega)]
      rw [← hs, hn]
      ring

/-- A normalized cumulant sequence is uniquely recovered from its complete
Bell family. -/
theorem eq_cumulant_of_complete {κ m : ℕ → R} (hκ0 : κ 0 = 0)
    (hcomp : complete κ = m) : κ = cumulant m := by
  have hm0 : m 0 = 1 := by
    rw [← hcomp]
    exact complete_zero κ
  refine eq_cumulant_of_recurrence hm0 hκ0 fun n => ?_
  calc
    m (n + 1) = complete κ (n + 1) := (congrFun hcomp (n + 1)).symm
    _ = binomialConv (complete κ) (shift κ) n := complete_succ κ n
    _ = binomialConv m (shift κ) n := by rw [hcomp]

/-- The first cumulant is the first moment. -/
@[simp]
theorem cumulant_one (m : ℕ → R) : cumulant m 1 = m 1 := by
  norm_num [cumulant]

/-- The second cumulant is `m₂ - m₁²`. -/
theorem cumulant_two (m : ℕ → R) : cumulant m 2 = m 2 - m 1 ^ 2 := by
  norm_num [cumulant]
  ring

/-- The third cumulant is `m₃ - 3m₁m₂ + 2m₁³`. -/
theorem cumulant_three (m : ℕ → R) :
    cumulant m 3 = m 3 - 3 * m 1 * m 2 + 2 * m 1 ^ 3 := by
  norm_num [cumulant, Finset.sum_range_succ]
  ring

end CommRing

end Bell
