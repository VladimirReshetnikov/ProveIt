import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Algebraic outputs as number-field integers

This module packages an algebraic complex number inside a number field together
with a nonzero natural denominator whose multiple is an algebraic integer.  The
real-valued wrappers make the package directly usable for algebraic outputs of
real exponential expressions.
-/

open scoped IntermediateField NumberField

noncomputable section

namespace LeanProofs.IntegerExponent

/-- A number-field realization of an algebraic complex value, together with a
nonzero natural denominator clearing its preimage to an algebraic integer. -/
structure AlgebraicOutputBridge (alpha : ℂ) where
  K : Type
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  embedding : K →+* ℂ
  preimage : K
  map_preimage : embedding preimage = alpha
  denominator : ℕ
  denominator_ne_zero : denominator ≠ 0
  integer : NumberField.RingOfIntegers K
  denominator_smul_preimage : denominator • preimage = (integer : K)

namespace AlgebraicOutputBridge

/-- The integral numerator in the bridge maps to the cleared complex value. -/
theorem denominator_smul_eq_map_integer {alpha : ℂ}
    (B : AlgebraicOutputBridge alpha) :
    B.denominator • alpha = B.embedding (B.integer : B.K) := by
  letI : Field B.K := B.fieldK
  letI : NumberField B.K := B.numberFieldK
  calc
    B.denominator • alpha = B.denominator • B.embedding B.preimage :=
      congrArg (B.denominator • ·) B.map_preimage.symm
    _ = B.embedding (B.denominator • B.preimage) := by simp
    _ = B.embedding (B.integer : B.K) :=
      congrArg B.embedding B.denominator_smul_preimage

/-- Realize an algebraic complex number in the simple number field it generates,
and clear its denominator to an algebraic integer of that number field. -/
def ofIsAlgebraic {alpha : ℂ} (halpha : IsAlgebraic ℚ alpha) :
    AlgebraicOutputBridge alpha := by
  let K : Type := ℚ⟮alpha⟯
  letI hfinite : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional halpha.isIntegral
  letI hnumber : NumberField K := NumberField.mk
  let a : K := IntermediateField.AdjoinSimple.gen ℚ alpha
  let sigma : K →+* ℂ := (IntermediateField.val ℚ⟮alpha⟯).toRingHom
  have ha : sigma a = alpha := by rfl
  have haQ : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have haZ : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr haQ
  let hex := haZ.exists_nsmul_eq (NumberField.RingOfIntegers K)
  let m : ℕ := Classical.choose hex
  have hmrest : ∃ z : NumberField.RingOfIntegers K,
      m ≠ 0 ∧ m • a = algebraMap (NumberField.RingOfIntegers K) K z :=
    Classical.choose_spec hex
  let z : NumberField.RingOfIntegers K := Classical.choose hmrest
  have hmz : m ≠ 0 ∧
      m • a = algebraMap (NumberField.RingOfIntegers K) K z :=
    Classical.choose_spec hmrest
  refine
    { K := K
      fieldK := inferInstance
      numberFieldK := hnumber
      embedding := sigma
      preimage := a
      map_preimage := ha
      denominator := m
      denominator_ne_zero := hmz.1
      integer := z
      denominator_smul_preimage := ?_ }
  simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap] using hmz.2

/-- The number-field bridge for a real algebraic value, viewed in `ℂ`. -/
def ofRealIsAlgebraic {alpha : ℝ} (halpha : IsAlgebraic ℚ alpha) :
    AlgebraicOutputBridge (alpha : ℂ) :=
  ofIsAlgebraic (halpha.algHom Complex.ofRealHom.toRatAlgHom)

/-- A nonzero natural multiple of every algebraic complex number is integral
over `ℤ`. -/
theorem exists_nsmul_isIntegral {alpha : ℂ} (halpha : IsAlgebraic ℚ alpha) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ (m • alpha) := by
  let B := ofIsAlgebraic halpha
  letI : Field B.K := B.fieldK
  letI : NumberField B.K := B.numberFieldK
  refine ⟨B.denominator, B.denominator_ne_zero, ?_⟩
  rw [B.denominator_smul_eq_map_integer]
  exact B.integer.property.map B.embedding.toIntAlgHom

/-- A nonzero natural multiple of every real algebraic number, viewed in `ℂ`,
is integral over `ℤ`. -/
theorem exists_nsmul_isIntegral_ofReal {alpha : ℝ}
    (halpha : IsAlgebraic ℚ alpha) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ (m • (alpha : ℂ)) :=
  exists_nsmul_isIntegral (halpha.algHom Complex.ofRealHom.toRatAlgHom)

end AlgebraicOutputBridge

end LeanProofs.IntegerExponent
