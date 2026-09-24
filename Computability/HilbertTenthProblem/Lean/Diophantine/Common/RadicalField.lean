import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# An algebraic field for integer square roots

The algebraic closure of the rationals contains square roots of every integer,
including negative integers. An embedding into the complex numbers lets later
arguments use absolute values without imposing a sign condition on the radicands.

Infinite Galois theory identifies the elements fixed by every rational
automorphism with the rationals. A fixed square root of an integer therefore
witnesses that the integer is a square, by the rational square criterion.
-/

namespace Diophantine

/-- A common field containing all square roots used in relation combining. -/
abbrev RadicalField := AlgebraicClosure ℚ

namespace RadicalField

private theorem closure_isGalois (K : Type*) [Field K] [CharZero K] :
    IsGalois K (AlgebraicClosure K) := inferInstance

/-- The quotient algebra and the canonical rational-cast algebra agree.
Transporting the generic instance avoids an algebra-instance diamond. -/
instance isGalois : IsGalois ℚ RadicalField := by
  convert closure_isGalois ℚ using 1
  apply Subsingleton.elim

/-- A fixed embedding for taking complex absolute values of algebraic roots. -/
noncomputable def toComplex : RadicalField →ₐ[ℚ] ℂ := IsAlgClosed.lift

theorem toComplex_injective : Function.Injective toComplex := toComplex.injective

@[simp] theorem toComplex_intCast (a : ℤ) : toComplex (a : RadicalField) = (a : ℂ) :=
  map_intCast toComplex a

@[simp] theorem toComplex_algebraMap (q : ℚ) :
    toComplex (algebraMap ℚ RadicalField q) = algebraMap ℚ ℂ q :=
  toComplex.commutes q

/-- Integer radicands need not be nonnegative in the algebraic closure. -/
theorem exists_sqrt (a : ℤ) : ∃ x : RadicalField, x ^ 2 = (a : RadicalField) :=
  IsAlgClosed.exists_pow_nat_eq (a : RadicalField) (by decide)

/-- Every element fixed by all rational automorphisms is rational. -/
theorem exists_rat_of_fixed {x : RadicalField}
    (h : ∀ σ : RadicalField ≃ₐ[ℚ] RadicalField, σ x = x) :
    ∃ q : ℚ, algebraMap ℚ RadicalField q = x :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) x).mpr h

/-- A rational square root of an integer is already an integer square root. -/
theorem isSquare_int_of_rat_sq {a : ℤ} {q : ℚ} (h : q ^ 2 = (a : ℚ)) :
    IsSquare a :=
  Rat.isSquare_intCast_iff.mp ⟨q, by simpa only [pow_two] using h.symm⟩

/-- Fixing an algebraic square root under all rational automorphisms forces
its integer radicand to be a square. -/
theorem isSquare_int_of_fixed {a : ℤ} {x : RadicalField}
    (hsq : x ^ 2 = (a : RadicalField))
    (hfixed : ∀ σ : RadicalField ≃ₐ[ℚ] RadicalField, σ x = x) :
    IsSquare a := by
  obtain ⟨q, hq⟩ := exists_rat_of_fixed hfixed
  apply isSquare_int_of_rat_sq (q := q)
  apply (algebraMap ℚ RadicalField).injective
  simpa only [map_pow, map_intCast, hq] using hsq

/-- A rational automorphism can only change the sign of an integer square root. -/
theorem aut_eq_or_eq_neg {a : ℤ} {x : RadicalField}
    (hsq : x ^ 2 = (a : RadicalField)) (σ : RadicalField ≃ₐ[ℚ] RadicalField) :
    σ x = x ∨ σ x = -x := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, hsq, map_intCast]

/-- The complex embedding preserves the specified square-root equation. -/
theorem toComplex_sq {a : ℤ} {x : RadicalField}
    (hsq : x ^ 2 = (a : RadicalField)) : (toComplex x) ^ 2 = (a : ℂ) := by
  rw [← map_pow, hsq, map_intCast]

end RadicalField

end Diophantine
