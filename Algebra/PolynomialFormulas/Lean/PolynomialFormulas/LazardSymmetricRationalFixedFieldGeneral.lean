import PolynomialFormulas.LazardGeneralResolventMinpoly
import PolynomialFormulas.LazardInvariantModule
import Mathlib.RingTheory.Invariant.Basic

/-!
# Symmetric rational functions over an arbitrary field

This is the field-generic form of the fixed-field theorem used in Lazard's
Section 3.  The older `LazardSymmetricRationalFixedField` file is intentionally
specialized to `ℚ`, because it is also part of the generic Abel--Ruffini
example.  Lazard's coefficient field `Q`, however, is an arbitrary field.

For a field `F`, this file proves

`F(X₀, ..., Xₙ₋₁) ^ Sₙ = F(e₁, ..., eₙ)`.

The action is the same variable-renaming action used by the general resolvent
development.  The proof uses `IsFractionRing.isInvariant`, so no fixed-field,
finite-extension, or Galois certificate is supplied by a caller.
-/

noncomputable section

namespace LeanProofs.PolynomialFormulas.LazardSymmetricRationalFixedFieldGeneral

open MvPolynomial

/-- The polynomial ring in `n` independent variables over `F`. -/
abbrev A (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Fin n) F

/-- Its rational-function field. -/
abbrev L (F : Type*) [Field F] (n : ℕ) := FractionRing (A F n)

/-- The full permutation group of the variables. -/
abbrev G (n : ℕ) := Equiv.Perm (Fin n)

/-- The symmetric polynomial subalgebra. -/
abbrev SymmetricA (F : Type*) [Field F] (n : ℕ) :=
  symmetricSubalgebra (Fin n) F

/-- The fraction field of the symmetric polynomial subalgebra. -/
abbrev SymmetricL (F : Type*) [Field F] (n : ℕ) :=
  FractionRing (SymmetricA F n)

section FixedField

variable (F : Type*) [Field F]
variable (n : ℕ)

/- Use exactly the action installed by the general resolvent development, so
the fixed field below composes definitionally with its minpoly theorem. -/
local instance polynomialRenameAction : MulSemiringAction (G n) (A F n) :=
  LazardGeneralResolventExplicit.polynomialRenameMulSemiringAction

local instance fractionRenameAction : MulSemiringAction (G n) (L F n) :=
  LazardGeneralResolventExplicit.fractionRenameMulSemiringAction

local instance fractionRenameActionAL : SMulDistribClass (G n) (A F n) (L F n) :=
  IsFractionRing.smulDistribClass (G n) (A F n) (L F n)

/-- The fixed field of all variable permutations. -/
abbrev FullFixedField := FixedPoints.subfield (G n) (L F n)

/-- Symmetric coefficients commute with permutation on the polynomial ring. -/
local instance permCommSymmetricA :
    SMulCommClass (G n) (SymmetricA F n) (A F n) where
  smul_comm σ s p := by
    change MvPolynomial.rename σ (s.1 * p) = s.1 * MvPolynomial.rename σ p
    rw [map_mul, s.2 σ]

/-- The symmetric polynomial ring is the full fixed polynomial ring. -/
local instance symmetricPolynomial_isInvariant :
    Algebra.IsInvariant (SymmetricA F n) (A F n) (G n) where
  isInvariant p hp := by
    refine ⟨⟨p, ?_⟩, rfl⟩
    intro σ
    exact hp σ

/- The canonical `Subalgebra.toAlgebra` instance is exactly the composite
`F[e] -> F[X] -> F(X)`, and `IsScalarTower.subalgebra` supplies its tower. -/

local instance symmetricPolynomialFaithfulL :
    FaithfulSMul (SymmetricA F n) (L F n) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y h
  apply Subtype.ext
  apply IsFractionRing.injective (A F n) (L F n)
  exact h

/-- Extend the symmetric-polynomial inclusion to fraction fields. -/
local instance symmetricFractionAlgebraL : Algebra (SymmetricL F n) (L F n) :=
  FractionRing.liftAlgebra (SymmetricA F n) (L F n)

local instance symmetricFractionTowerL :
    IsScalarTower (SymmetricA F n) (SymmetricL F n) (L F n) :=
  FractionRing.isScalarTower_liftAlgebra (SymmetricA F n) (L F n)

local instance permCommSymmetricL :
    SMulCommClass (G n) (SymmetricL F n) (L F n) :=
  IsFractionRing.smulCommClass
    (G n) (SymmetricA F n) (A F n) (SymmetricL F n) (L F n)

local instance symmetricFraction_isInvariant :
    Algebra.IsInvariant (SymmetricL F n) (L F n) (G n) :=
  IsFractionRing.isInvariant
    (G n) (SymmetricA F n) (A F n) (SymmetricL F n) (L F n)

/-- Field-generic symmetric rational fixed-field identity. -/
theorem fixedField_eq_symmetricFraction_fieldRange :
    FullFixedField F n =
      (algebraMap (SymmetricL F n) (L F n)).fieldRange := by
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_fieldRange]
    exact Algebra.IsInvariant.isInvariant x hx
  · rw [RingHom.mem_fieldRange]
    rintro ⟨y, rfl⟩ σ
    exact smul_algebraMap σ y

/-- The symmetric rational-function extension has the expected finite
degree.  This is a consequence of the faithful permutation action, not a
finite-extension certificate supplied by a caller. -/
theorem fullFixedField_finrank_eq_factorial :
    Module.finrank (FullFixedField F n) (L F n) = n.factorial := by
  rw [FixedPoints.finrank_eq_card, Fintype.card_perm, Fintype.card_fin]

/-- The rational-function field is Galois over its full symmetric fixed
field.  Mathlib derives this from the finite faithful action. -/
theorem fullFixedField_isGalois :
    IsGalois (FullFixedField F n) (L F n) :=
  IsGaloisGroup.isGalois (G n) (FullFixedField F n) (L F n)

/-- Every automorphism over the full symmetric fixed field is induced by a
unique permutation of the variables. -/
noncomputable def symmetricGroupEquivFullGalois :
    G n ≃* (L F n ≃ₐ[FullFixedField F n] L F n) :=
  FixedPoints.toAlgAutMulEquiv (G n) (L F n)

/-- Paper-facing bundle of the fixed-field, finite-degree, and Galois
claims for the generic symmetric rational-function extension. -/
theorem sectionThreeFixedFieldAndGalois :
    FullFixedField F n =
        (algebraMap (SymmetricL F n) (L F n)).fieldRange ∧
      Module.finrank (FullFixedField F n) (L F n) = n.factorial ∧
      IsGalois (FullFixedField F n) (L F n) :=
  ⟨fixedField_eq_symmetricFraction_fieldRange F n,
    fullFixedField_finrank_eq_factorial F n,
    fullFixedField_isGalois F n⟩

end FixedField

/-- The symmetric fraction field is a rational-function field in the
elementary symmetric generators, over the same arbitrary base field. -/
noncomputable def elementarySymmetricFractionEquiv
    (F : Type*) [Field F] (n : ℕ) :
    FractionRing (MvPolynomial (Fin n) F) ≃ₐ[F] SymmetricL F n :=
  IsFractionRing.algEquivOfAlgEquiv
    (MvPolynomial.esymmAlgEquiv (Fin n) F (Fintype.card_fin n))

@[simp] theorem elementarySymmetricFractionEquiv_algebraMap_X
    (F : Type*) [Field F] (n : ℕ) (i : Fin n) :
    elementarySymmetricFractionEquiv F n
        (algebraMap (MvPolynomial (Fin n) F)
          (FractionRing (MvPolynomial (Fin n) F)) (X i)) =
      algebraMap (SymmetricA F n) (SymmetricL F n)
        ⟨esymm (Fin n) F (i + 1), esymm_isSymmetric (Fin n) F (i + 1)⟩ := by
  rw [elementarySymmetricFractionEquiv,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp [MvPolynomial.esymmAlgEquiv, MvPolynomial.esymmAlgHom]

end LeanProofs.PolynomialFormulas.LazardSymmetricRationalFixedFieldGeneral
