import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact arithmetic attached to the Fabius function

This file keeps the arithmetic part of Arias de Reyna's paper in `ℚ` and `ℕ`.
In particular, no denominator or `p`-adic valuation is ever taken of a real
number.  Later analytic theorems connect these exact quantities to the bounded
Fabius function and to Rvachev's `up` function.

The definitions follow equations (10), (19), (27), and (32) of
*Arithmetic of the Fabius function* (arXiv:1702.06487v3).  The exponent in the
definition of `reshetnikov` is the positive exponent appearing in equation
(27); the arXiv abstract has a sign typo.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ### Triangular numbers

`Nat.choose n 2` is the `n`-th triangular number, and it appears throughout
this development as the exponent of a power of two: in `dyadicScale`, in the
Thue--Morse block weights, in the flatness constants `2 ^ C(n+1,2)`, and in
every q-binomial formula.  The step and square identities below were
previously re-proved privately in ten places under ten different names; they
are stated once here because `Arithmetic` is the only module every consumer
already imports. -/

/-- The triangular step identity: `C(n+1, 2) = C(n, 2) + n`.

This is `Nat.choose_succ_succ` followed by `Nat.choose_one_right`, but it is
used often enough, and in enough modules that share no ancestor but this one,
to deserve a name. -/
theorem choose_succ_two (n : ℕ) :
    (n + 1).choose 2 = n.choose 2 + n := by
  rw [show n + 1 = Nat.succ n by omega, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm]

/-- Twice a triangular number plus its index is a square:
`2 * C(n, 2) + n = n ^ 2`.

Equivalently `C(n, 2) = n(n-1)/2`, stated without natural subtraction or
division so that it can be transported into any semiring by `push_cast`. -/
theorem two_mul_choose_two_add (n : ℕ) :
    2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : 2 * (n + 1).choose 2 + (n + 1)
          = (2 * n.choose 2 + n) + (2 * n + 1) := by
        rw [choose_succ_two]
        ring
      rw [hstep, ih]
      ring

/-- The shifted form of `choose_succ_two`, stated at `n + 2` because several
dyadic recursions index their blocks from one rather than zero. -/
theorem choose_add_two_two (n : ℕ) :
    (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) :=
  choose_succ_two (n + 1)

/-- The sum of the binary digits of `n`, denoted `w(n)` in the paper. -/
def binaryWeight (n : ℕ) : ℕ :=
  (Nat.digits 2 n).sum

/-- The Thue--Morse sign `(-1)^w(n)`. -/
def thueMorseSign (n : ℕ) : ℤ :=
  (-1) ^ binaryWeight n

/-- The product `∏_{j=a}^{b-1} (2j+1)`. -/
def oddFactorProduct (a b : ℕ) : ℕ :=
  ∏ j ∈ Ico a b, (2 * j + 1)

/-- The product `∏_{j=a}^{b-1} (2^j-1)`. -/
def mersenneIntervalProduct (a b : ℕ) : ℕ :=
  ∏ j ∈ Ico a b, (2 ^ j - 1)

/-- The product `1 * 3 * ... * (2n - 1)`, with value `1` at `n = 0`. -/
def oddDoubleFactorial (n : ℕ) : ℕ :=
  ∏ k ∈ range n, (2 * k + 1)

/-- Split `(2n)!` into its even and odd factors. -/
theorem factorial_two_mul_eq (n : ℕ) :
    (2 * n).factorial = 2 ^ n * n.factorial * oddDoubleFactorial n := by
  induction n with
  | zero => simp [oddDoubleFactorial]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n), ih,
        pow_succ, Nat.factorial_succ n]
      simp only [oddDoubleFactorial, Finset.prod_range_succ]
      ring

/-- The product `∏_{k=1}^n (2^k - 1)`. -/
def mersenneProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range n, (2 ^ (k + 1) - 1)

/-- The product `∏_{k=1}^n (2^(2k) - 1)`. -/
def evenMersenneProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range n, (2 ^ (2 * (k + 1)) - 1)

/-- The product `∏_{k=0}^n (2^(2k+1) - 1)`. -/
def oddMersenneProduct (n : ℕ) : ℕ :=
  ∏ k ∈ range (n + 1), (2 ^ (2 * k + 1) - 1)

/-! ### Structural facts about the normalization products -/

/-- Append the final odd factor to an odd double factorial. -/
theorem oddDoubleFactorial_succ (n : ℕ) :
    oddDoubleFactorial (n + 1) = oddDoubleFactorial n * (2 * n + 1) := by
  simp [oddDoubleFactorial, Finset.prod_range_succ]

/-- Append the final factor to the ordinary Mersenne product. -/
theorem mersenneProduct_succ_eq (n : ℕ) :
    mersenneProduct (n + 1) = mersenneProduct n * (2 ^ (n + 1) - 1) := by
  simp [mersenneProduct, Finset.prod_range_succ]

/-- Append the final factor to the even-indexed Mersenne product. -/
theorem evenMersenneProduct_succ_eq (n : ℕ) :
    evenMersenneProduct (n + 1) =
      evenMersenneProduct n * (2 ^ (2 * (n + 1)) - 1) := by
  simp [evenMersenneProduct, Finset.prod_range_succ]

/-- Append the final factor to the odd-indexed Mersenne product. -/
theorem oddMersenneProduct_succ_eq (n : ℕ) :
    oddMersenneProduct (n + 1) =
      oddMersenneProduct n * (2 ^ (2 * (n + 1) + 1) - 1) := by
  simp [oddMersenneProduct, Finset.prod_range_succ]

/-- Odd double factorials are positive, including the empty product. -/
theorem oddDoubleFactorial_pos (n : ℕ) : 0 < oddDoubleFactorial n := by
  unfold oddDoubleFactorial
  exact Finset.prod_pos fun k _ => by omega

/-- Ordinary Mersenne products are positive, including the empty product. -/
theorem mersenneProduct_pos (n : ℕ) : 0 < mersenneProduct n := by
  unfold mersenneProduct
  apply Finset.prod_pos
  intro k hk
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))

/-- Even-indexed Mersenne products are positive, including the empty product. -/
theorem evenMersenneProduct_pos (n : ℕ) : 0 < evenMersenneProduct n := by
  unfold evenMersenneProduct
  apply Finset.prod_pos
  intro k hk
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))

/-- Odd-indexed Mersenne products are positive. -/
theorem oddMersenneProduct_pos (n : ℕ) : 0 < oddMersenneProduct n := by
  unfold oddMersenneProduct
  apply Finset.prod_pos
  intro k hk
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))

/-- A finite product of odd natural numbers is odd. -/
theorem finset_prod_odd {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (by
        intro i hi
        exact hf i (by simp [hi])))

/-- A positive power of two minus one is odd. -/
theorem two_pow_sub_one_odd {e : ℕ} (he : 0 < e) : Odd (2 ^ e - 1) := by
  apply Nat.Even.sub_odd Nat.one_le_two_pow
  · exact Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt he⟩
  · exact odd_one

/-- Every odd double factorial is odd. -/
theorem odd_oddDoubleFactorial (n : ℕ) : Odd (oddDoubleFactorial n) := by
  unfold oddDoubleFactorial
  apply finset_prod_odd
  intro k hk
  exact odd_two_mul_add_one k

/-- Every ordinary Mersenne product is odd. -/
theorem odd_mersenneProduct (n : ℕ) : Odd (mersenneProduct n) := by
  unfold mersenneProduct
  apply finset_prod_odd
  intro k hk
  exact two_pow_sub_one_odd (by omega)

/-- Every even-indexed Mersenne product is odd. -/
theorem odd_evenMersenneProduct (n : ℕ) : Odd (evenMersenneProduct n) := by
  unfold evenMersenneProduct
  apply finset_prod_odd
  intro k hk
  exact two_pow_sub_one_odd (by omega)

/-- Every odd-indexed Mersenne product is odd. -/
theorem odd_oddMersenneProduct (n : ℕ) : Odd (oddMersenneProduct n) := by
  unfold oddMersenneProduct
  apply finset_prod_odd
  intro k hk
  exact two_pow_sub_one_odd (by omega)

/-- A rational number is the image of a natural number. -/
def IsNatural (q : ℚ) : Prop :=
  ∃ m : ℕ, q = m

/-- A rational number is the image of an odd natural number. -/
def IsOddNatural (q : ℚ) : Prop :=
  ∃ m : ℕ, Odd m ∧ q = m

/-! ### Odd reduced denominators -/

/-- The sum of rationals with odd reduced denominators again has odd reduced
denominator. -/
theorem rat_den_add_odd {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q + r).den :=
  (hq.mul hr).of_dvd_nat (Rat.add_den_dvd q r)

/-- The product of rationals with odd reduced denominators again has odd
reduced denominator. -/
theorem rat_den_mul_odd {q r : ℚ} (hq : Odd q.den) (hr : Odd r.den) :
    Odd (q * r).den :=
  (hq.mul hr).of_dvd_nat (Rat.mul_den_dvd q r)

/-- A finite sum of rationals with odd reduced denominators has odd reduced
denominator. -/
theorem rat_den_sum_odd {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, Odd (f i).den) : Odd (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply rat_den_add_odd (hf a (by simp))
      exact ih (by
        intro i hi
        exact hf i (by simp [hi]))

/-- Dividing by an odd natural preserves oddness of the reduced denominator. -/
theorem rat_den_div_nat_odd (q : ℚ) (d : ℕ)
    (hq : Odd q.den) (hd : Odd d) : Odd (q / (d : ℚ)).den := by
  rw [div_eq_mul_inv]
  apply rat_den_mul_odd hq
  rw [Rat.inv_natCast_den_of_pos hd.pos]
  exact hd

/-- The reduced denominator of a quotient of natural numbers divides its
displayed denominator. -/
theorem rat_den_dvd_nat_div (a b : ℕ) :
    ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have hInt :
      ((((a : ℚ) / (b : ℚ)).den : ℕ) : ℤ) ∣ (b : ℤ) := by
    rw [Rat.natCast_div_eq_divInt]
    exact Rat.den_dvd a b
  exact_mod_cast hInt

/-- If multiplication by a natural number makes a rational integral, then
the rational's reduced denominator divides that natural number.  The
statement includes the zero multiplier, where divisibility is automatic. -/
theorem rat_den_dvd_of_mul_nat_eq_int {q : ℚ} {B : ℕ} {z : ℤ}
    (h : q * (B : ℚ) = (z : ℚ)) : q.den ∣ B := by
  by_cases hB : B = 0
  · subst B
    exact dvd_zero _
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hq : q = (z : ℚ) / (B : ℚ) := (eq_div_iff hBq).2 h
  have hdivInt : q = Rat.divInt z (B : ℤ) := by
    rw [hq, Rat.divInt_eq_div]
    norm_num
  have hdvdInt : (q.den : ℤ) ∣ (B : ℤ) := by
    rw [hdivInt]
    exact Rat.den_dvd z B
  exact_mod_cast hdvdInt

/--
The rational moment sequence `c_n`, defined by the recurrence in equation
(10).  Strong recursion makes the recurrence itself the executable
specification and keeps later arithmetic proofs independent of integration.
-/
def moment : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
          (Nat.choose (2 * (n + 1) + 1) (2 * k.val) : ℚ) * moment k.val) /
        (((2 * (n + 1) + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * (n + 1)) - 1))
termination_by n => n
decreasing_by exact k.isLt

/--
The rational half-moment sequence `d_n`, defined by equation (19).
-/
def halfMoment : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) /
        (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1))
termination_by n => n
decreasing_by exact k.isLt

@[simp]
theorem moment_zero : moment 0 = 1 := by
  rw [moment]

@[simp]
theorem halfMoment_zero : halfMoment 0 = 1 := by
  rw [halfMoment]

/-- The recurrence equation for a positive-index moment. -/
theorem moment_succ (n : ℕ) :
    moment (n + 1) =
      (∑ k : Fin (n + 1),
        (Nat.choose (2 * (n + 1) + 1) (2 * k.val) : ℚ) * moment k.val) /
        (((2 * (n + 1) + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * (n + 1)) - 1)) := by
  rw [moment]

/-- The recurrence equation for a positive-index half moment. -/
theorem halfMoment_succ (n : ℕ) :
    halfMoment (n + 1) =
      (∑ k : Fin (n + 1),
        (Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) /
        (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1)) := by
  rw [halfMoment]

/-- Every recursively defined half moment is strictly positive. -/
theorem halfMoment_pos (n : ℕ) : 0 < halfMoment n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => norm_num
      | succ n =>
          rw [halfMoment_succ]
          apply div_pos
          · apply Finset.sum_pos
            · intro k hk
              exact mul_pos (by
                exact_mod_cast Nat.choose_pos (by omega : k.val ≤ n + 2))
                (ih k.val k.isLt)
            · exact ⟨0, Finset.mem_univ _⟩
          · exact mul_pos (by positivity) (sub_pos.mpr
              (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega)))

/--
The natural sequence `F_n` from Proposition 1.  This is the integral recurrence
(13), with quotients of double factorials replaced by interval products.
-/
def momentNumerator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k : Fin (n + 1),
        momentNumerator k.val * Nat.choose (2 * (n + 1) + 1) (2 * k.val) *
          oddFactorProduct (k.val + 1) (n + 1) *
          (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1))
termination_by n => n
decreasing_by exact k.isLt

/-- The division-free recurrence defining `F_(n+1)`. -/
theorem momentNumerator_succ (n : ℕ) :
    momentNumerator (n + 1) =
      ∑ k : Fin (n + 1),
        momentNumerator k.val * Nat.choose (2 * (n + 1) + 1) (2 * k.val) *
          oddFactorProduct (k.val + 1) (n + 1) *
          (∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1)) := by
  rw [momentNumerator]

/--
The natural sequence `G_n` from Proposition 4, defined by the recurrence in
its proof.  Factorial quotients are represented by interval products.
-/
def halfMomentNumerator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k : Fin (n + 1),
        halfMomentNumerator k.val * Nat.choose (n + 2) k.val *
          (∏ j ∈ Ico (k.val + 2) (n + 2), j) *
          mersenneIntervalProduct (k.val + 1) (n + 1)
termination_by n => n
decreasing_by exact k.isLt

/-- The division-free recurrence defining `G_(n+1)`. -/
theorem halfMomentNumerator_succ (n : ℕ) :
    halfMomentNumerator (n + 1) =
      ∑ k : Fin (n + 1),
        halfMomentNumerator k.val * Nat.choose (n + 2) k.val *
          (∏ j ∈ Ico (k.val + 2) (n + 2), j) *
          mersenneIntervalProduct (k.val + 1) (n + 1) := by
  rw [halfMomentNumerator]

/-- The exact rational value corresponding to `F(2⁻ⁿ)`, from equation (22). -/
def halfMomentFabiusValue (n : ℕ) : ℚ :=
  halfMoment n / ((n.factorial : ℚ) * (2 : ℚ) ^ n.choose 2)

/--
Equation (32): the exact rational value of `F(a / 2^n)`.

The analytic bridge is stated for `a ≤ 2^n`.  The formula itself is useful for
exact computation and is total on natural inputs.
-/
def fabiusDyadic (n a : ℕ) : ℚ :=
  (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial *
    ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
      ∑ k : Fin (n / 2 + 1),
        (Nat.choose n (2 * k.val) : ℚ) *
          ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) * moment k.val

/-- The exact rational value corresponding to `F(2⁻ⁿ)`. -/
def fabiusAtInverseTwoPow (n : ℕ) : ℚ :=
  fabiusDyadic n 1

/-! ## Executable evaluation at arbitrary dyadic arguments -/

/--
The table `[F(1), F(1/2), ..., F(2⁻ⁿ)]`, computed by the recurrence used in
Reshetnikov's exact evaluator.

Keeping the already-computed prefix in an array avoids the repeated unfolding
of `halfMoment` that a direct recursive implementation would perform.
-/
def fabiusInversePowTwoTable : (n : ℕ) → Array ℚ
  | 0 => #[1]
  | n + 1 =>
      let previous := fabiusInversePowTwoTable n
      previous.push <|
        (∑ k : Fin (n + 1),
            (previous[k.val]?).getD 0 /
              ((2 : ℚ) ^ ((n + 1).choose 2 - k.val.choose 2) *
                ((n + 1 - k.val + 1).factorial : ℚ))) /
          ((2 : ℚ) ^ (n + 1) - 1)

/-- Read an inverse-power value from a precomputed table. -/
def fabiusInversePowTwoTableValue (values : Array ℚ) (n : ℕ) : ℚ :=
  (values[n]?).getD 0

/--
Horner evaluation of the Taylor polynomial about `2⁻ᵒʳᵈᵉʳ` used in
Proposition 10.  A table containing at least the entries through `order` is
expected; the public evaluator below always supplies such a table.
-/
def fabiusTaylorHorner (values : Array ℚ) (order : ℕ) (offset : ℚ) : ℚ :=
  let rec go : ℕ → ℚ
    | 0 => 1
    | m + 1 =>
        fabiusInversePowTwoTableValue values (m + 1) +
          ((2 : ℚ) ^ (order - m) * offset / (order - m)) * go m
  go order

/--
The bit-recursive core of the exact dyadic evaluator on `[0,1]`.

At every recursive call the highest set bit of `numerator` is removed.  Thus
evaluation terminates after at most the number of set bits in the numerator,
instead of summing over every smaller numerator as equation (32) does.
Numerators at or above `2^exponent` are clamped to `1`.
-/
def fabiusDyadicUnitAux (values : Array ℚ) (exponent : ℕ) : ℕ → ℚ
  | 0 => 0
  | a + 1 =>
      if 2 ^ exponent ≤ a + 1 then
        1
      else
        let leadingExponent := Nat.log2 (a + 1)
        let order := exponent - leadingExponent
        let remainder := a + 1 - 2 ^ leadingExponent
        let offset := (remainder : ℚ) / (2 : ℚ) ^ exponent
        fabiusTaylorHorner values order offset -
          fabiusDyadicUnitAux values exponent remainder
termination_by a => a
decreasing_by
  apply Nat.sub_lt (Nat.zero_lt_succ a)
  positivity

/-- Exact bounded Fabius value at the natural dyadic `numerator / 2^exponent`. -/
def fabiusDyadicUnit (exponent numerator : ℕ) : ℚ :=
  if numerator = 0 then
    0
  else if 2 ^ exponent ≤ numerator then
    1
  else
    fabiusDyadicUnitAux (fabiusInversePowTwoTable exponent) exponent numerator

/--
Compute the bounded/CDF Fabius function exactly at any signed dyadic argument
`numerator / 2^exponent`.

This is the principal total evaluator for the project's convention: values at
nonpositive arguments are `0`, values at arguments at least `1` are `1`, and
the interior is evaluated by Reshetnikov's terminating Taylor recursion.
-/
def fabiusDyadicValue (exponent : ℕ) (numerator : ℤ) : ℚ :=
  if numerator ≤ 0 then 0 else fabiusDyadicUnit exponent numerator.toNat

@[simp]
theorem fabiusDyadicUnit_zero (exponent : ℕ) :
    fabiusDyadicUnit exponent 0 = 0 := by
  simp [fabiusDyadicUnit]

theorem fabiusDyadicUnit_of_ge (exponent numerator : ℕ)
    (h : 2 ^ exponent ≤ numerator) :
    fabiusDyadicUnit exponent numerator = 1 := by
  simp [fabiusDyadicUnit, h, Nat.ne_of_gt (lt_of_lt_of_le (by positivity) h)]

@[simp]
theorem fabiusDyadicValue_zero (exponent : ℕ) :
    fabiusDyadicValue exponent 0 = 0 := by
  simp [fabiusDyadicValue]

theorem fabiusDyadicValue_of_nonpos (exponent : ℕ) (numerator : ℤ)
    (h : numerator ≤ 0) :
    fabiusDyadicValue exponent numerator = 0 := by
  simp [fabiusDyadicValue, h]

theorem fabiusDyadicValue_of_ge (exponent : ℕ) (numerator : ℤ)
    (h : (2 ^ exponent : ℤ) ≤ numerator) :
    fabiusDyadicValue exponent numerator = 1 := by
  have hpos : 0 < numerator := lt_of_lt_of_le (by positivity) h
  have hnat : 2 ^ exponent ≤ numerator.toNat := by
    apply (Int.le_toNat hpos.le).2
    simpa using h
  simp [fabiusDyadicValue, fabiusDyadicUnit, not_le_of_gt hpos, hnat]

/--
Compute the paper's signed global extension exactly at any dyadic argument.

Positive arguments are reduced to `[0,1]` using the triangular reduction
modulo `2` and the Thue--Morse sign.  Nonpositive arguments are `0`.  This is
separate from `fabiusDyadicValue`, since the bounded function is instead
constant `1` to the right of the unit interval.
-/
def extendedFabiusDyadicValue (exponent : ℕ) (numerator : ℤ) : ℚ :=
  if numerator ≤ 0 then
    0
  else
    let scale := 2 ^ exponent
    let period := 2 * scale
    let naturalNumerator := numerator.toNat
    let block := naturalNumerator / period
    let residue := naturalNumerator % period
    let coreNumerator := if residue ≤ scale then residue else period - residue
    (thueMorseSign block : ℚ) * fabiusDyadicUnit exponent coreNumerator

@[simp]
theorem extendedFabiusDyadicValue_zero (exponent : ℕ) :
    extendedFabiusDyadicValue exponent 0 = 0 := by
  simp [extendedFabiusDyadicValue]

theorem extendedFabiusDyadicValue_of_nonpos (exponent : ℕ) (numerator : ℤ)
    (h : numerator ≤ 0) :
    extendedFabiusDyadicValue exponent numerator = 0 := by
  simp [extendedFabiusDyadicValue, h]

/-- A rational is dyadic when its reduced denominator is a power of two. -/
def IsDyadicRational (x : ℚ) : Prop :=
  ∃ exponent : ℕ, x.den = 2 ^ exponent

/--
Return the denominator exponent when a reduced rational is dyadic.

For example, the exponent of `5/16` is `4`; a non-dyadic rational such as
`2/3` returns `none`.
-/
def dyadicExponent? (x : ℚ) : Option ℕ :=
  let exponent := x.den.log2
  if x.den = 2 ^ exponent then some exponent else none

/--
Evaluate the bounded Fabius function on a rational input when it is dyadic.
The result is an explicit reduced rational; `none` certifies that the input's
reduced denominator is not a power of two.
-/
def evalFabiusDyadic (x : ℚ) : Option ℚ :=
  match dyadicExponent? x with
  | none => none
  | some exponent => some (fabiusDyadicValue exponent x.num)

/-- Rational-input wrapper for the signed global dyadic evaluator. -/
def evalExtendedFabiusDyadic (x : ℚ) : Option ℚ :=
  match dyadicExponent? x with
  | none => none
  | some exponent => some (extendedFabiusDyadicValue exponent x.num)

/--
The exact value of `up(a / 2^n)` for an integer numerator.  Evenness reduces
negative arguments to nonnegative ones; values outside the support are zero.
The absolute value records the nonnegative codomain of Rvachev's function in
the exact representation.  The analytic bridge proves it is extensionally
redundant whenever a bounded Fabius function is supplied.
-/
def rvachevDyadic (n : ℕ) (a : ℤ) : ℚ :=
  if a.natAbs ≤ 2 ^ n then
    |fabiusDyadic n (2 ^ n - a.natAbs)|
  else
    0

/-- The positive odd numerators at dyadic level `n`. -/
def oddDyadicNumerators (n : ℕ) : Finset ℕ :=
  (Icc 1 (2 ^ n - 1)).filter Odd

/-- Reflection about the midpoint permutes the positive odd dyadic grid. -/
theorem oddDyadicNumerators_reflect_mem (n a : ℕ) (hn : 1 ≤ n)
    (ha : a ∈ oddDyadicNumerators n) :
    2 ^ n - a ∈ oddDyadicNumerators n := by
  have ha_filter := (mem_filter.mp (show
    a ∈ (Icc 1 (2 ^ n - 1)).filter Odd by simpa [oddDyadicNumerators] using ha))
  have ha_bounds := Finset.mem_Icc.mp ha_filter.1
  have haodd := ha_filter.2
  rw [oddDyadicNumerators, mem_filter, Finset.mem_Icc]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  apply Nat.Even.sub_odd (by omega) _ haodd
  exact Nat.even_pow.mpr ⟨even_two, by omega⟩

/-- The equivalent LCM formed from bounded Fabius values on the odd grid. -/
def fabiusDyadicDenominator (n : ℕ) : ℕ :=
  (oddDyadicNumerators n).lcm fun a => (fabiusDyadic n a).den

/--
The paper's `D_n`: the LCM of denominators of Rvachev `up` on the positive
odd level-`n` dyadic grid (Definition 12).
-/
def dyadicDenominator (n : ℕ) : ℕ :=
  (oddDyadicNumerators n).lcm fun a => (rvachevDyadic n a).den

/--
Reshetnikov's rational number `R_n` (equation (27)).  Its mathematically
intended domain is `n ≥ 1`; the definition is made total only for convenience.
-/
def reshetnikov (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (n - 1).choose 2 * (Nat.factorial (2 * n) : ℚ) *
    fabiusAtInverseTwoPow n * evenMersenneProduct (n / 2)

/-- The explicit common-denominator bound in Theorem 13. -/
def denominatorBound (n : ℕ) : ℕ :=
  n.factorial * 2 ^ (n + 1).choose 2 * oddDoubleFactorial (n / 2 + 1) *
    evenMersenneProduct (n / 2)

/-- The rational normalization `A_n = 2^(-choose n 2) D_n`. -/
def normalizedDyadicDenominator (n : ℕ) : ℚ :=
  dyadicDenominator n / (2 : ℚ) ^ n.choose 2

/-- The sequence `K_n = A_(2n-1)` from Conjecture 16. -/
def conjecturalK (n : ℕ) : ℚ :=
  normalizedDyadicDenominator (2 * n - 1)

/-- The sequence `H_n = K_n / (2 (2n-1)!)` from Conjecture 16. -/
def conjecturalH (n : ℕ) : ℚ :=
  conjecturalK n / (2 * (Nat.factorial (2 * n - 1) : ℚ))

end Fabius
