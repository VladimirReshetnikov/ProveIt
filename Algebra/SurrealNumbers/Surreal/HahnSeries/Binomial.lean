import Surreal.HahnSeries.Evaluation
import Mathlib.RingTheory.HahnSeries.Binomial

/-!
# Admissible binomial expansions near one

The binomial specialization of `a:cor:complexsub` is a Hahn-summable family
whose actual terms are `Ring.choose r n • x ^ n` for a positive-order `x`.
Its sum has constant coefficient one and differs from one by positive order.
The formal exponent-addition and natural-exponent identities remain valid
after this admissible substitution.

The rational root formula is the algebraic identity used in the proof of
`b:ramification` and in the local binomial expansions of the trigonometry
report (for example, the proof of `trigonometry:eq:flatslack`). It constructs
an `m`th root near one. It does not identify a globally defined power or the
positive square root in an ordered surreal field, and asserts no topological
convergence or local analytic normal form.

Mathlib's total binomial family has a fallback outside the admissible domain.
Every definition here requires a positive-order witness, and the term theorem
checks that the family is the intended binomial substitution.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R A : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

section BinomialRing

variable [CommRing R] [BinomialRing R] [CommRing A] [Algebra R A]

/-- The actual summable binomial family at a positive-order argument,
licensed by `a:cor:complexsub`. -/
def binomialTerms (x : A⟦Γ⟧) (_hx : 0 < x.orderTop) (r : R) :
    SummableFamily Γ A ℕ :=
  SummableFamily.binomialFamily (1 + x) r

/-- The admissibility witness excludes Mathlib's fallback and identifies
every term of the family with the intended binomial term. -/
@[simp] theorem binomialTerms_apply (x : A⟦Γ⟧) (hx : 0 < x.orderTop)
    (r : R) (n : ℕ) : binomialTerms x hx r n = Ring.choose r n • x ^ n := by
  have hadm : 0 < ((1 + x) - 1).orderTop := by simpa using hx
  rw [binomialTerms, SummableFamily.binomialFamily_apply hadm, add_sub_cancel_left]

/-- The formal binomial expansion of `1 + x`, evaluated only on the
positive-order domain from `a:cor:complexsub`. -/
def binomialPower (x : A⟦Γ⟧) (hx : 0 < x.orderTop) (r : R) : A⟦Γ⟧ :=
  evaluate x hx (PowerSeries.binomialSeries A r)

/-- The evaluated binomial power is the Hahn sum of the actual family. -/
theorem binomialPower_eq_hsum (x : A⟦Γ⟧) (hx : 0 < x.orderTop) (r : R) :
    binomialPower x hx r = (binomialTerms x hx r).hsum := by
  simp only [binomialPower, evaluate, PowerSeries.heval_apply, binomialTerms,
    SummableFamily.binomialFamily, add_sub_cancel_left]

/-- The constant coefficient of every admissible binomial power is one. -/
@[simp] theorem coeff_zero_binomialPower (x : A⟦Γ⟧) (hx : 0 < x.orderTop) (r : R) :
    (binomialPower x hx r).coeff 0 = 1 := by
  simp only [binomialPower, coeff_zero_evaluate, PowerSeries.binomialSeries_constantCoeff]

/-- An admissible binomial power remains in the positive-order
neighborhood of one, including the zero increment case. -/
theorem orderTop_binomialPower_sub_one_pos (x : A⟦Γ⟧)
    (hx : 0 < x.orderTop) (r : R) :
    0 < (binomialPower x hx r - 1).orderTop := by
  rw [binomialPower_eq_hsum]
  exact SummableFamily.orderTop_hsum_binomialFamily_pos (by simpa using hx) r

/-- Exponent addition is multiplication of the admissible binomial sums. -/
theorem binomialPower_add (x : A⟦Γ⟧) (hx : 0 < x.orderTop) (r s : R) :
    binomialPower x hx (r + s) = binomialPower x hx r * binomialPower x hx s := by
  simp only [binomialPower, PowerSeries.binomialSeries_add, map_mul]

/-- Natural exponents agree with ordinary finite powers of `1 + x`. -/
@[simp] theorem binomialPower_nat (x : A⟦Γ⟧) (hx : 0 < x.orderTop) (n : ℕ) :
    binomialPower x hx (n : R) = (1 + x) ^ n := by
  simp only [binomialPower, PowerSeries.binomialSeries_nat, map_pow, map_add, map_one,
    evaluate_X]

@[simp] theorem binomialPower_zero (x : A⟦Γ⟧) (hx : 0 < x.orderTop) :
    binomialPower x hx (0 : R) = 1 := by
  simpa only [Nat.cast_zero, pow_zero] using binomialPower_nat (R := R) x hx 0

@[simp] theorem binomialPower_one (x : A⟦Γ⟧) (hx : 0 < x.orderTop) :
    binomialPower x hx (1 : R) = 1 + x := by
  simpa only [Nat.cast_one, pow_one] using binomialPower_nat (R := R) x hx 1

/-- Raising an admissible binomial sum to a natural power multiplies
its formal exponent. -/
theorem binomialPower_pow (x : A⟦Γ⟧) (hx : 0 < x.orderTop) (r : R) (n : ℕ) :
    binomialPower x hx r ^ n = binomialPower x hx ((n : R) * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, binomialPower_add]

end BinomialRing

section RationalRoots

variable [CommRing A] [Algebra ℚ A]

/-- The rational binomial `m`th-root identity used in the proof of
`b:ramification`. This concerns the root near one furnished by an actual
Hahn sum; neither root selection in an ordered field nor ramification of
analytic germs is asserted. -/
theorem binomialPower_rat_root (x : A⟦Γ⟧) (hx : 0 < x.orderTop)
    (m : ℕ) (hm : m ≠ 0) :
    binomialPower x hx (1 / (m : ℚ)) ^ m = 1 + x := by
  rw [binomialPower_pow, mul_one_div_cancel (Nat.cast_ne_zero.mpr hm), binomialPower_one]

/-- The square-root binomial sum used for the local expansions in the
trigonometry report squares to `1 + x`. -/
theorem binomialPower_half_sq (x : A⟦Γ⟧) (hx : 0 < x.orderTop) :
    binomialPower x hx (1 / 2 : ℚ) ^ 2 = 1 + x :=
  binomialPower_rat_root x hx 2 (by decide)

end RationalRoots

end
end Surreal.HahnSeries
