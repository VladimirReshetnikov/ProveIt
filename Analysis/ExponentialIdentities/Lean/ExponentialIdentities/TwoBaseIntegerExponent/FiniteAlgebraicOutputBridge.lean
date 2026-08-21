import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# A common number field for finitely many algebraic outputs

This file packages a finite family of algebraic complex values inside one number
field.  One nonzero natural denominator simultaneously clears every chosen
preimage to an algebraic integer.
-/

open scoped IntermediateField NumberField

noncomputable section

namespace LeanProofs.IntegerExponent

/-- A common number-field realization of a family of complex values, with one
nonzero natural denominator clearing every preimage to `𝒪 K`. -/
structure FiniteAlgebraicOutputBridge {I : Type*} (alpha : I → ℂ) where
  K : Type
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  embedding : K →+* ℂ
  preimage : I → K
  map_preimage : ∀ i, embedding (preimage i) = alpha i
  denominator : ℕ
  denominator_ne_zero : denominator ≠ 0
  integer : I → NumberField.RingOfIntegers K
  denominator_smul_preimage :
    ∀ i, denominator • preimage i = (integer i : K)

namespace FiniteAlgebraicOutputBridge

/-- The common denominator identity after applying the distinguished embedding. -/
theorem denominator_smul_eq_map_integer {I : Type*} {alpha : I → ℂ}
    (B : FiniteAlgebraicOutputBridge alpha) (i : I) :
    B.denominator • alpha i = B.embedding (B.integer i : B.K) := by
  letI : Field B.K := B.fieldK
  letI : NumberField B.K := B.numberFieldK
  calc
    B.denominator • alpha i = B.denominator • B.embedding (B.preimage i) :=
      congrArg (B.denominator • ·) (B.map_preimage i).symm
    _ = B.embedding (B.denominator • B.preimage i) := by simp
    _ = B.embedding (B.integer i : B.K) :=
      congrArg B.embedding (B.denominator_smul_preimage i)

/-- Put a finite family of algebraic complex values in their common finite
extension of `ℚ`, and clear all denominators by one nonzero natural number. -/
def ofIsAlgebraic {I : Type*} [Finite I] {alpha : I → ℂ}
    (halpha : ∀ i, IsAlgebraic ℚ (alpha i)) :
    FiniteAlgebraicOutputBridge alpha := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let K : Type := IntermediateField.adjoin ℚ (Set.range alpha)
  letI hfinite : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun z hz ↦ by
      obtain ⟨i, rfl⟩ := hz
      exact (halpha i).isIntegral
  letI hnumber : NumberField K := NumberField.mk
  let sigma : K →+* ℂ :=
    (IntermediateField.val (IntermediateField.adjoin ℚ (Set.range alpha))).toRingHom
  let a : I → K := fun i ↦
    ⟨alpha i, IntermediateField.subset_adjoin ℚ (Set.range alpha) ⟨i, rfl⟩⟩
  have ha : ∀ i, sigma (a i) = alpha i := fun _ ↦ rfl
  letI hAlgZ : Algebra.IsAlgebraic ℤ K :=
    ⟨fun y ↦ (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
      (Algebra.IsAlgebraic.isAlgebraic y)⟩
  let hex :=
    Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image a)
  let z : ℤ := Classical.choose hex
  have hzrest : z ≠ 0 ∧
      ∀ y ∈ Finset.univ.image a, IsIntegral ℤ (z • y) :=
    Classical.choose_spec hex
  have hz0 : z ≠ 0 := hzrest.1
  have hzint : ∀ y ∈ Finset.univ.image a, IsIntegral ℤ (z • y) :=
    hzrest.2
  have ha_mem (i : I) : a i ∈ Finset.univ.image a := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  cases hz : z with
  | ofNat m =>
      simp only [hz] at hz0 hzint
      have hm0 : m ≠ 0 := by simpa using hz0
      have hmInt (i : I) : IsIntegral ℤ (m • a i) := by
        simpa using hzint (a i) (ha_mem i)
      let integer : I → NumberField.RingOfIntegers K :=
        fun i ↦ ⟨m • a i, hmInt i⟩
      exact
        { K := K
          fieldK := inferInstance
          numberFieldK := hnumber
          embedding := sigma
          preimage := a
          map_preimage := ha
          denominator := m
          denominator_ne_zero := hm0
          integer := integer
          denominator_smul_preimage := fun _ ↦ rfl }
  | negSucc m =>
      simp only [hz] at hz0 hzint
      have hmInt (i : I) : IsIntegral ℤ ((m + 1) • a i) := by
        have hneg : IsIntegral ℤ (-((m + 1) • a i)) := by
          simpa only [negSucc_zsmul] using hzint (a i) (ha_mem i)
        exact hneg.of_neg
      let integer : I → NumberField.RingOfIntegers K :=
        fun i ↦ ⟨(m + 1) • a i, hmInt i⟩
      exact
        { K := K
          fieldK := inferInstance
          numberFieldK := hnumber
          embedding := sigma
          preimage := a
          map_preimage := ha
          denominator := m + 1
          denominator_ne_zero := by omega
          integer := integer
          denominator_smul_preimage := fun _ ↦ rfl }

/-- Specialization placing six algebraic outputs in one common bridge. -/
def ofFinSixIsAlgebraic {alpha : Fin 6 → ℂ}
    (halpha : ∀ i, IsAlgebraic ℚ (alpha i)) :
    FiniteAlgebraicOutputBridge alpha :=
  ofIsAlgebraic halpha

end FiniteAlgebraicOutputBridge

end LeanProofs.IntegerExponent
