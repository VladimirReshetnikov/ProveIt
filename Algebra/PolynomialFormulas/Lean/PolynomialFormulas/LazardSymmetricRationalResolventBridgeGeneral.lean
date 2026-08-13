import PolynomialFormulas.LazardSymmetricRationalFixedFieldGeneral

/-!
# Field-generic symmetric-rational resolvent bridge

This composes the arbitrary-base-field fixed-field identity with the general
exact-stabilizer orbit/minimal-polynomial theorem.  The only mathematical
input is the exact renaming stabilizer of the chosen invariant; fixed-field
identification, ordinary minimal-polynomial equality, and subgroup-fixed-field
generation are derived.
-/

noncomputable section

open scoped Polynomial
open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardSymmetricRationalResolventBridgeGeneral

namespace General
export LazardSymmetricRationalFixedFieldGeneral
  (A L G SymmetricA SymmetricL FullFixedField
    fixedField_eq_symmetricFraction_fieldRange
    fullFixedField_finrank_eq_factorial fullFixedField_isGalois)
end General

namespace Resolvent
export LazardGeneralResolventExplicit
  (ExactRootTuplePresentation fractionInvariant_adjoin_eq_fixedPoints
    fractionRenameMulSemiringAction HasExactRenameStabilizer
    hasExactRenameStabilizer_iff_generator_and_minpoly InvariantUnder
    paperRootTupleResolvent paperRootTupleResolvent_hasRoot_iff_image_le_conjugate
    polynomialRenameMulSemiringAction rootTupleAction universalInvariantResolvent
    universalInvariantResolvent_map_fraction_eq_minpoly)
end Resolvent

namespace Criterion
export LazardGeneralResolventCriterion (conjugateStabilizer)
end Criterion

universe uA

/- Keep the quotient enumeration definitionally aligned with the one used by
`LazardGeneralResolventMinpoly`.  Those instances are local to that source
file, so importing its theorems does not make them available here. -/
noncomputable local instance quotientSubgroupDecidablePred
    {A : Type uA} [Group A] [Fintype A] (H : Subgroup A) :
    DecidablePred (fun x : A => x ∈ H) := Classical.decPred _

noncomputable local instance quotientDecidableRel
    {A : Type uA} [Group A] [Fintype A] (H : Subgroup A) :
    DecidableRel (QuotientGroup.leftRel H) :=
  QuotientGroup.leftRelDecidable H

noncomputable local instance quotientFintype
    {A : Type uA} [Group A] [Fintype A] (H : Subgroup A) :
    Fintype (A ⧸ H) :=
  QuotientGroup.fintype H

section SymmetricEmbedding

variable (F : Type*) [Field F]
variable (n : ℕ)

local instance polynomialRenameAction :
    MulSemiringAction (General.G n) (General.A F n) :=
  Resolvent.polynomialRenameMulSemiringAction

local instance fractionRenameAction :
    MulSemiringAction (General.G n) (General.L F n) :=
  Resolvent.fractionRenameMulSemiringAction

/- Use the canonical composite algebra and scalar tower supplied for a
subalgebra, as in the fixed-field module. -/

local instance symmetricPolynomialFaithfulL :
    FaithfulSMul (General.SymmetricA F n) (General.L F n) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y h
  apply Subtype.ext
  apply IsFractionRing.injective (General.A F n) (General.L F n)
  exact h

local instance symmetricFractionAlgebraL :
    Algebra (General.SymmetricL F n) (General.L F n) :=
  FractionRing.liftAlgebra (General.SymmetricA F n) (General.L F n)

local instance symmetricFractionTowerL :
    IsScalarTower
      (General.SymmetricA F n) (General.SymmetricL F n) (General.L F n) :=
  FractionRing.isScalarTower_liftAlgebra
    (General.SymmetricA F n) (General.L F n)

/-- The intrinsic full fixed field is the embedded arbitrary-base elementary-
symmetric rational-function field. -/
theorem fullFixedField_eq_elementarySymmetricFractionRange :
    General.FullFixedField F n =
      (algebraMap (General.SymmetricL F n) (General.L F n)).fieldRange := by
  exact General.fixedField_eq_symmetricFraction_fieldRange F n

theorem mem_fullFixedField_iff_exists_elementarySymmetricFraction
    (x : General.L F n) :
    x ∈ General.FullFixedField F n ↔
      ∃ y : General.SymmetricL F n,
        algebraMap (General.SymmetricL F n) (General.L F n) y = x := by
  rw [fullFixedField_eq_elementarySymmetricFractionRange F n,
    RingHom.mem_fieldRange]

section LiteralDefinition

variable (H : Subgroup (General.G n))
variable (p : General.A F n)
variable (hpH : Resolvent.InvariantUnder H p)

/-- Paper-facing iff for Lazard's literal definition of a resolvent
invariant over the elementary-symmetric rational-function field.  Exact
renaming stabilizer is equivalent to fixed-field generation together with
the ordinary minimal-polynomial identity.  The minimal-polynomial conjunct
is intentionally retained to mirror the paper, although generation alone
proves the reverse implication. -/
theorem exactStabilizer_iff_literalResolventDefinition :
    Resolvent.HasExactRenameStabilizer H p ↔
      IntermediateField.adjoin (General.FullFixedField F n)
          {algebraMap (General.A F n) (General.L F n) p} =
          (FixedPoints.intermediateField H :
            IntermediateField (General.FullFixedField F n) (General.L F n)) ∧
        (Resolvent.universalInvariantResolvent H p hpH).map
            (algebraMap (General.A F n) (General.L F n)) =
          (_root_.minpoly (General.FullFixedField F n)
            (algebraMap (General.A F n) (General.L F n) p)).map
            (algebraMap (General.FullFixedField F n) (General.L F n)) := by
  exact Resolvent.hasExactRenameStabilizer_iff_generator_and_minpoly H p hpH

end LiteralDefinition

section ExactInvariant

variable (H : Subgroup (General.G n))
variable (p : General.A F n)
variable (hp : Resolvent.HasExactRenameStabilizer H p)

theorem universalResolvent_map_eq_minpoly_over_fullFixedField :
    (Resolvent.universalInvariantResolvent H p hp.invariantUnder).map
        (algebraMap (General.A F n) (General.L F n)) =
      (_root_.minpoly (General.FullFixedField F n)
        (algebraMap (General.A F n) (General.L F n) p)).map
        (algebraMap (General.FullFixedField F n) (General.L F n)) := by
  exact Resolvent.universalInvariantResolvent_map_fraction_eq_minpoly H p hp

include hp in
theorem exactInvariant_adjoin_eq_fixedField :
    IntermediateField.adjoin (General.FullFixedField F n)
        {algebraMap (General.A F n) (General.L F n) p} =
      (FixedPoints.intermediateField H :
        IntermediateField (General.FullFixedField F n) (General.L F n)) := by
  exact Resolvent.fractionInvariant_adjoin_eq_fixedPoints H p hp

/-- Complete field-generic composition: literal elementary-symmetric base,
ordinary minimal polynomial, and generation of the exact subgroup fixed
field. -/
theorem exactInvariant_resolvent_minpoly_and_generator :
    General.FullFixedField F n =
        (algebraMap (General.SymmetricL F n) (General.L F n)).fieldRange ∧
      (Resolvent.universalInvariantResolvent H p hp.invariantUnder).map
          (algebraMap (General.A F n) (General.L F n)) =
        (_root_.minpoly (General.FullFixedField F n)
          (algebraMap (General.A F n) (General.L F n) p)).map
          (algebraMap (General.FullFixedField F n) (General.L F n)) ∧
      IntermediateField.adjoin (General.FullFixedField F n)
          {algebraMap (General.A F n) (General.L F n) p} =
        (FixedPoints.intermediateField H :
          IntermediateField (General.FullFixedField F n) (General.L F n)) := by
  refine ⟨fullFixedField_eq_elementarySymmetricFractionRange F n,
    universalResolvent_map_eq_minpoly_over_fullFixedField F n H p hp, ?_⟩
  exact exactInvariant_adjoin_eq_fixedField F n H p hp

end ExactInvariant

section SectionThreeAndTheoremOne

variable {L : Type*} [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]
variable (H : Subgroup (General.G n))
variable (p : General.A F n)
variable (hp : Resolvent.HasExactRenameStabilizer H p)
variable (f : F[X]) (roots : Fin n → L)
variable (presentation :
  Resolvent.ExactRootTuplePresentation f roots)

/-- A single paper-shaped composition of the symmetric rational fixed-field
theorem, the literal resolvent-definition clauses, and the corrected
root-labelling form of Theorem 1.

The caller supplies the mathematical data that the paper itself selects: an
invariant with exact formal stabilizer, an exact ordering of the roots, and
separability of the *specialized* resolvent for the converse.  The full
symmetric fixed field, degree, Galois property, ordinary minimal polynomial,
subgroup-fixed-field generation, root permutation action, equivariance, and
specialized orbit factorization are all derived internally.  The converse
conclusion is containment in a conjugate of `H`; the forward fixed-`H`
implication remains available separately without separability. -/
theorem sectionThreeAndTheoremOne_exactInvariantRootCriterion
    (hseparable :
      (Resolvent.paperRootTupleResolvent
        (G := H) (invariant := p) (f := f) (roots := roots)
        (exactStabilizer := hp)
        (exactPresentation := presentation)).Separable) :
    General.FullFixedField F n =
        (algebraMap (General.SymmetricL F n) (General.L F n)).fieldRange ∧
      Module.finrank (General.FullFixedField F n) (General.L F n) =
        n.factorial ∧
      IsGalois (General.FullFixedField F n) (General.L F n) ∧
      (Resolvent.universalInvariantResolvent H p hp.invariantUnder).map
          (algebraMap (General.A F n) (General.L F n)) =
        (_root_.minpoly (General.FullFixedField F n)
          (algebraMap (General.A F n) (General.L F n) p)).map
          (algebraMap (General.FullFixedField F n) (General.L F n)) ∧
      IntermediateField.adjoin (General.FullFixedField F n)
          {algebraMap (General.A F n) (General.L F n) p} =
        (FixedPoints.intermediateField H :
          IntermediateField (General.FullFixedField F n) (General.L F n)) ∧
      ((∃ q : F,
          (Resolvent.paperRootTupleResolvent
            (G := H) (invariant := p) (f := f) (roots := roots)
            (exactStabilizer := hp)
            (exactPresentation := presentation)).IsRoot q) ↔
        ∃ a : General.G n,
          (Resolvent.rootTupleAction f roots
            presentation.toRootTuplePresentation).range ≤
              Criterion.conjugateStabilizer H a) := by
  refine ⟨General.fixedField_eq_symmetricFraction_fieldRange F n,
    General.fullFixedField_finrank_eq_factorial F n,
    General.fullFixedField_isGalois F n,
    Resolvent.universalInvariantResolvent_map_fraction_eq_minpoly H p hp,
    Resolvent.fractionInvariant_adjoin_eq_fixedPoints H p hp, ?_⟩
  exact Resolvent.paperRootTupleResolvent_hasRoot_iff_image_le_conjugate
    (G := H) (invariant := p) (f := f) (roots := roots)
    (exactStabilizer := hp) (exactPresentation := presentation) hseparable

end SectionThreeAndTheoremOne

end SymmetricEmbedding

end LeanProofs.PolynomialFormulas.LazardSymmetricRationalResolventBridgeGeneral
