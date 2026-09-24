import Surreal.Algebra.GaussianQuotientCardinality
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Ordinary Gaussian prime quotients

Ordinary coefficient-ring input to `osq:cor:smallprimes`.
The Gaussian integers are not a field, and their prime-element quotients
are finite fields. These statements are independent of surreal numbers.
-/

namespace Surreal.GaussianQuotientCardinality

/-- Every map from Gaussian integers to a characteristic-zero ring is injective. -/
theorem ringHom_injective_charZero {R : Type*} [Ring R] [CharZero R]
    (φ : GaussianInt →+* R) : Function.Injective φ := by
  apply (injective_iff_map_eq_zero φ).mpr
  intro z hz
  have hn : (z.norm : R) = 0 := by
    rw [← map_intCast φ, Zsqrtd.norm_eq_mul_conj, map_mul, hz, zero_mul]
  exact GaussianInt.norm_eq_zero.mp (Int.cast_eq_zero.mp hn)

/-- The Gaussian integer ring is not a field: two is a nonzero nonunit. -/
theorem not_isField : ¬ IsField GaussianInt := by
  intro h
  letI := h.toField
  have hu : IsUnit (2 : GaussianInt) := isUnit_iff_ne_zero.mpr (by norm_num)
  have hn := (Zsqrtd.isUnit_iff_norm_isUnit (2 : GaussianInt)).mp hu
  norm_num [Int.isUnit_iff, Zsqrtd.norm] at hn

/-- Each Gaussian prime generates a maximal ordinary Gaussian ideal. -/
theorem prime_span_isMaximal (d : GaussianInt) (hd : Prime d) :
    (Ideal.span {d}).IsMaximal := by
  letI : (Ideal.span {d}).IsPrime := (Ideal.span_singleton_prime hd.ne_zero).mpr hd
  exact IsPrime.to_maximal_ideal (fun h => hd.ne_zero (Ideal.span_singleton_eq_bot.mp h))

/-- A Gaussian prime quotient is a finite field of its already computed norm cardinality. -/
theorem prime_quotient (d : GaussianInt) (hd : Prime d) :
    IsField (GaussianInt ⧸ Ideal.span {d}) ∧ Finite (GaussianInt ⧸ Ideal.span {d}) ∧
      Nat.card (GaussianInt ⧸ Ideal.span {d}) = d.norm.natAbs :=
  ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (prime_span_isMaximal d hd),
    finite_quotient d hd.ne_zero, card_quotient d⟩

end Surreal.GaussianQuotientCardinality
