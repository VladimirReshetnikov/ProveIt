import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Polynomial.Basic

/-!
# Real algebraic integers exclude nonzero finite ring targets

The generic obstruction in `osq:nm:thm:nofinite`. For every n ≥ 2,
the monic integer polynomial X^n - X - 1 has a real root between zero
and two. Such roots cannot map to finite fields. Passing through the
kernel quotient and a maximal ideal also excludes noncommutative finite
ring targets. This argument uses only ordinary real algebraic integers.
-/

namespace Surreal.NormalizationFiniteTargets
open Polynomial
noncomputable section

/-- A real algebraic integer between zero and two solves x^n = x + 1 for every n ≥ 2. -/
theorem exists_integral_pow_eq_add_one (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : ℝ, x ∈ Set.Ioo 0 2 ∧ IsIntegral ℤ x ∧ x ^ n = x + 1 := by
  have hn0 : n ≠ 0 := by omega
  have hp : (2 : ℝ) ^ 2 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  obtain ⟨x, hx, he⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ 2 by norm_num)
    (f := fun x : ℝ => x ^ n - x - 1) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Ioo (0 ^ n - 0 - 1) (2 ^ n - 2 - 1) by
      constructor
      · simp [hn0]
      · norm_num at hp ⊢
        linarith)
  refine ⟨x, hx, ?_, by linarith⟩
  refine ⟨X ^ n - (X + 1), ?_, ?_⟩
  · apply monic_X_pow_sub
    rw [← C_1, degree_X_add_C]
    exact_mod_cast (show 1 < n by omega)
  · simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_add, eval₂_one,
      sub_add_eq_sub_sub] using he

/-- Rings with these power-equation solutions cannot map to a finite field. -/
theorem no_finite_field_hom {A K : Type*} [CommRing A] [Field K] [Finite K]
    (hroot : ∀ n : ℕ, 2 ≤ n → ∃ x : A, x ^ n = x + 1) (f : A →+* K) : False := by
  letI := Fintype.ofFinite K
  obtain ⟨x, hx⟩ := hroot (Fintype.card K) Fintype.one_lt_card
  have he := congrArg f hx
  simp only [map_pow, map_add, map_one, FiniteField.pow_card] at he
  exact one_ne_zero (add_left_cancel (show f x + 1 = f x + 0 by simpa using he.symm))

/-- The obstruction includes finite targets that are not commutative and arbitrary target universes. -/
theorem no_finite_ring_hom {A R : Type*} [CommRing A] [Ring R] [Finite R] [Nontrivial R]
    (hroot : ∀ n : ℕ, 2 ≤ n → ∃ x : A, x ^ n = x + 1) (f : A →+* R) : False := by
  letI : Finite (A ⧸ RingHom.ker f) :=
    Finite.of_injective f.quotientKerEquivRange f.quotientKerEquivRange.injective
  letI : Nontrivial (A ⧸ RingHom.ker f) :=
    f.quotientKerEquivRange.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⧸ RingHom.ker f)
  letI := hm
  letI := Ideal.Quotient.field m
  letI : Finite ((A ⧸ RingHom.ker f) ⧸ m) :=
    Finite.of_surjective (Ideal.Quotient.mk m) Ideal.Quotient.mk_surjective
  exact no_finite_field_hom hroot ((Ideal.Quotient.mk m).comp (Ideal.Quotient.mk (RingHom.ker f)))

/-- The native ring of real algebraic integers has no nonzero finite ring target. -/
theorem realAlgebraicIntegers_no_finite_ring_hom {R : Type*}
    [Ring R] [Finite R] [Nontrivial R] (f : integralClosure ℤ ℝ →+* R) : False := by
  apply no_finite_ring_hom (f := f)
  intro n hn
  obtain ⟨x, _, hx, he⟩ := exists_integral_pow_eq_add_one n hn
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- Any ring receiving the real algebraic integers has the same finite-target obstruction. -/
theorem no_finite_ring_hom_of_realAlgebraicIntegers {A R : Type*} [Ring A]
    [Ring R] [Finite R] [Nontrivial R]
    (ι : integralClosure ℤ ℝ →+* A) (f : A →+* R) : False :=
  realAlgebraicIntegers_no_finite_ring_hom (f.comp ι)

/-- Real algebraic integers map into the normalization of any real-containing commutative algebra. -/
def realAlgebraicIntegersToNormalization {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (ι : ℝ →+* A) : integralClosure ℤ ℝ →+* integralClosure B A :=
  (ι.comp (integralClosure ℤ ℝ).val.toRingHom).codRestrict (integralClosure B A).toSubring
    (fun x => (map_isIntegral_int ι x.property).tower_top)

@[simp] theorem realAlgebraicIntegersToNormalization_value {B A : Type*}
    [CommRing B] [CommRing A] [Algebra B A] (ι : ℝ →+* A) (x : integralClosure ℤ ℝ) :
    (realAlgebraicIntegersToNormalization (B := B) ι x : A) = ι x := rfl

/-- Every such normalization excludes all nonzero finite ring targets. -/
theorem normalization_no_finite_ring_hom {B A R : Type*}
    [CommRing B] [CommRing A] [Algebra B A] [Ring R] [Finite R] [Nontrivial R]
    (ι : ℝ →+* A) (f : integralClosure B A →+* R) : False :=
  no_finite_ring_hom_of_realAlgebraicIntegers (realAlgebraicIntegersToNormalization ι) f

/-- A finite quotient of a ring receiving real algebraic integers must be the zero ring. -/
theorem finite_quotient_eq_top {A : Type*} [CommRing A]
    (ι : integralClosure ℤ ℝ →+* A) (J : Ideal A) [Finite (A ⧸ J)] : J = ⊤ := by
  by_contra h
  letI := Ideal.Quotient.nontrivial_iff.mpr h
  exact no_finite_ring_hom_of_realAlgebraicIntegers ι (Ideal.Quotient.mk J)

/-- Every proper ideal of such a ring has an infinite quotient. -/
theorem infinite_quotient_of_ne_top {A : Type*} [CommRing A]
    (ι : integralClosure ℤ ℝ →+* A) (J : Ideal A) (hJ : J ≠ ⊤) : Infinite (A ⧸ J) := by
  apply not_finite_iff_infinite.mp
  intro h
  exact hJ (finite_quotient_eq_top ι J)

end
end Surreal.NormalizationFiniteTargets
