import Surreal.Surcomplex.BinaryFormRigidity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Pell rigidity over the actual omnific integers

The full `odg:cor:pell`: for every nonzero ordinary integer D and every
nonzero ordinary integer level, the omnific solutions of x² - D y² = c
are exactly the ordinary integer solutions. No positivity or nonsquare
assumption on D is needed.
-/

universe u
namespace Surreal.Surcomplex

open Foundations BinaryFormRigidity MvPolynomial

noncomputable section

/-- The native binary norm polynomial. -/
def pellPolynomial {R : Type*} [CommRing R] (D : R) : MvPolynomial (Fin 2) R :=
  X 0 ^ 2 - C D * X 1 ^ 2

/-- The two linear factors of a binary norm polynomial over a field with a chosen square root. -/
theorem pellPolynomial_factor {K : Type*} [Field K] (r : K) :
    pellPolynomial (r ^ 2) = linearForm 1 r * linearForm 1 (-r) := by
  simp only [pellPolynomial, linearForm, map_one, map_neg, map_pow]
  ring

/-- A nonzero complex norm parameter gives two projectively distinct factors. -/
theorem pellPolynomial_hasTwoProjectiveFactors (D : ℂ) (hD : D ≠ 0) :
    HasTwoProjectiveFactors (pellPolynomial D) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq D zero_lt_two
  have hrn : r ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hr
    exact hD hr.symm
  refine ⟨1, r, 1, -r, ?_, ?_, ?_⟩
  · intro h
    have he : (2 : ℂ) * r = 0 := by linear_combination -h
    exact mul_ne_zero two_ne_zero hrn he
  · rw [← hr, pellPolynomial_factor]
    exact dvd_mul_right _ _
  · rw [← hr, pellPolynomial_factor]
    exact dvd_mul_left _ _

/-- Integer coefficient extension retains the binary norm polynomial. -/
theorem pellPolynomial_map (D : ℤ) :
    (pellPolynomial D).map (Int.castRingHom ℂ) = pellPolynomial (D : ℂ) := by
  simp [pellPolynomial]

/-- Every actual omnific Pell solution at a nonzero integer level is its ordinary constant pair. -/
theorem omnific_pell_rigidity (D c : ℤ) (hD : D ≠ 0) (hc : c ≠ 0)
    (x y : SignSequence.OmnificInteger.{u})
    (h : x ^ 2 - SignSequence.omnificIntCast D * y ^ 2 = SignSequence.omnificIntCast c) :
    x = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff x) ∧
      y = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff y) := by
  let v : Fin 2 → SignSequence.OmnificInteger := ![x, y]
  have hp : HasTwoProjectiveFactors ((pellPolynomial D).map (Int.castRingHom ℂ)) := by
    rw [pellPolynomial_map]
    exact pellPolynomial_hasTwoProjectiveFactors (D : ℂ) (Int.cast_ne_zero.mpr hD)
  have he : (pellPolynomial D).eval₂ SignSequence.omnificIntCast v =
      SignSequence.omnificIntCast c := by
    simpa only [pellPolynomial, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_C, eval₂_X,
      v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using h
  obtain ⟨a, _, ha⟩ := (omnific_integer_binary_solutions_iff _ hp c hc v).mp he
  have hconst (k : Fin 2) : v k =
      SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff (v k)) := by
    rw [ha k, SignSequence.omnificConstantCoeff_intCast]
  exact ⟨hconst 0, hconst 1⟩

/-- The exact equality with the ordinary integer solution set, including its ordinary equation. -/
theorem omnific_pell_solutions_iff (D c : ℤ) (hD : D ≠ 0) (hc : c ≠ 0)
    (x y : SignSequence.OmnificInteger.{u}) :
    x ^ 2 - SignSequence.omnificIntCast D * y ^ 2 = SignSequence.omnificIntCast c ↔
      ∃ a b : ℤ, a ^ 2 - D * b ^ 2 = c ∧
        x = SignSequence.omnificIntCast a ∧ y = SignSequence.omnificIntCast b := by
  constructor
  · intro h
    have he := omnific_pell_rigidity D c hD hc x y h
    refine ⟨SignSequence.omnificConstantCoeff x, SignSequence.omnificConstantCoeff y, ?_, he⟩
    have hr := congrArg SignSequence.omnificConstantCoeff h
    simpa only [map_sub, map_pow, map_mul, SignSequence.omnificConstantCoeff_intCast] using hr
  · rintro ⟨a, b, h, rfl, rfl⟩
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, h]

end
end Surreal.Surcomplex
