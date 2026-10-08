import GowersSzemeredi.Proofs16PolynomialAllScaleLemma6
import GowersSzemeredi.Proofs16PolynomialRecurrenceComparison
import GowersSzemeredi.Proofs16ParametricLineExponent

/-! The polynomial line-width exponent eventually improves the old one.

This comparison includes the extra constant loss used to absorb the new
recurrence threshold at every scale. The dimension constants and crossover
remain existential. It compares line-width exponents, not the final
all-length Szemeredi threshold or the complete small-scale width functions.
-/
set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

def section16PolynomialLemma9Exponent (k p q : Nat) (sigma theta gamma a : Real) : Real :=
  ((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
    section16Lemma9R theta gamma k * a) /
      (4 * ((2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real))

/-- The improved all-scale Lemma 16.9 width in prefactor-times-power form. -/
theorem section16PolynomialLemma9Width_eq_power (m k C p q : Nat)
    (sigma theta gamma a zeta : Real) :
    section16PolynomialLinearityWidth m k C p q
      (((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
        section16Lemma9R theta gamma k) * a) zeta =
      (zeta / (4 * ((C * (q + 1) : Nat) : Real))) *
        (m : Real) ^ section16PolynomialLemma9Exponent k p q sigma theta gamma a := rfl

/-- Positivity of the new line exponent for positive controls. -/
theorem section16PolynomialLemma9Exponent_pos {k p q : Nat}
    (hk : 0 < k) (hp : 0 < p) {sigma theta gamma a : Real}
    (hs : 0 < sigma) (ht : 0 < theta) (hg : 0 < gamma) (ha : 0 < a) :
    0 < section16PolynomialLemma9Exponent k p q sigma theta gamma a := by
  have hh := lemma9WidthWithExponent_pos hk hs ht hg ha 0
  simp only [lemma9WidthWithExponent, section16RecurrenceExponent, Nat.mul_zero,
    Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hh
  unfold section16PolynomialLemma9Exponent
  apply div_pos _ (by positivity)
  linarith

/-- The factor-two all-scale exponent loss still leaves an eventual strict
improvement over the old line exponent for fixed positive controls. -/
theorem eventually_lemma9WidthWithExponent_lt_polynomial {k p : Nat}
    (hk : 0 < k) (hp : 0 < p) {sigma theta gamma a : Real}
    (hs : 0 < sigma) (ht : 0 < theta) (hg : 0 < gamma) (ha : 0 < a) :
    ∀ᶠ q : Nat in atTop,
      lemma9WidthWithExponent q k sigma theta gamma a <
        section16PolynomialLemma9Exponent k p q sigma theta gamma a := by
  have h := eventually_section16RecurrenceExponent_lt_simultaneous k (2 * p) (by positivity)
  let f := (multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
    section16Lemma9R theta gamma k * a
  have hf : 0 < f := by
    have hh := lemma9WidthWithExponent_pos hk hs ht hg ha 0
    simp only [lemma9WidthWithExponent, section16RecurrenceExponent, Nat.mul_zero,
      Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hh
    dsimp [f]
    linarith
  filter_upwards [h] with q hq
  have hmul := mul_lt_mul_of_pos_left hq (div_pos hf (by norm_num : (0 : Real) < 2))
  calc
    lemma9WidthWithExponent q k sigma theta gamma a =
        (f / 2) * section16RecurrenceExponent k q := by
      unfold lemma9WidthWithExponent f
      ring
    _ < (f / 2) * section16SimultaneousExponent k (2 * p) q := hmul
    _ = section16PolynomialLemma9Exponent k p q sigma theta gamma a := by
      unfold section16SimultaneousExponent section16PolynomialLemma9Exponent f
      push_cast
      ring

end LeanProofs.GowersSzemeredi
