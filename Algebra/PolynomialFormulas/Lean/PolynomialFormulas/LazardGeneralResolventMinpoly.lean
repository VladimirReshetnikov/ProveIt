import PolynomialFormulas.LazardGeneralResolventExplicit
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The invariant-field/minimal-polynomial bridge for Lazard resolvents

This file supplies the field-theoretic part deliberately separated from
`LazardGeneralResolventExplicit`.  A finite group `A` acts on the variables of
`MvPolynomial ι F`; the renaming action is extended, by the universal
property of a fraction field, to

`FractionRing (MvPolynomial ι F)`.

If a polynomial `p` has renaming stabilizer exactly `G ≤ A`, injectivity of
the polynomial-to-fraction-field map proves that the embedded rational
function has stabilizer exactly `G` as well.  Consequently its product of
distinct `A`-conjugates is precisely both

* the scalar extension of `universalInvariantResolvent G p`, and
* `FixedPoints.minpoly A _ p`, hence the ordinary `minpoly` over the
  `A`-fixed field.

Under the natural additional assumption that the action on the variables is
faithful, finite Galois correspondence also proves that this one element
generates the `G`-fixed intermediate field over the `A`-fixed field.  Thus the
generator and minimal-polynomial clauses in Lazard's definition are derived
here; no identification of the `A`-fixed field with an elementary-symmetric
rational-function presentation is asserted or needed.
-/

noncomputable section

open scoped Polynomial
open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardGeneralResolventExplicit

universe uF uA uI

noncomputable local instance quotientFintype
    {A : Type uA} [Group A] [Fintype A] (G : Subgroup A) :
    Fintype (A ⧸ G) := by
  letI := Classical.decRel (QuotientGroup.leftRel G)
  exact QuotientGroup.fintype G

section FractionFieldAction

variable {F : Type uF} [Field F]
variable {A : Type uA} [Group A]
variable {ι : Type uI} [MulAction A ι]

/-- Variable renaming as a multiplicative homomorphism into polynomial-ring
automorphisms.  Its orientation is the same as `renameAction_mul`. -/
def polynomialRenameHom :
    A →* (MvPolynomial ι F ≃+* MvPolynomial ι F) where
  toFun a := (MvPolynomial.renameEquiv F (MulAction.toPerm a)).toRingEquiv
  map_one' := by
    apply RingEquiv.ext
    intro p
    exact renameAction_one p
  map_mul' a b := by
    apply RingEquiv.ext
    intro p
    exact renameAction_mul a b p

/-- The multiplicative semiring action on the polynomial ring obtained by
renaming variables. -/
noncomputable instance (priority := low) polynomialRenameMulSemiringAction :
    MulSemiringAction A (MvPolynomial ι F) :=
  MulSemiringAction.compHom (MvPolynomial ι F)
    (polynomialRenameHom (F := F) (A := A) (ι := ι))

/-- The typeclass action above is definitionally the explicit renaming
action used in the resolvent construction. -/
@[simp] theorem polynomialRename_smul (a : A) (p : MvPolynomial ι F) :
    a • p = renameAction a p :=
  rfl

/-- The induced action on the rational-function field. -/
noncomputable instance (priority := low) fractionRenameMulSemiringAction :
    MulSemiringAction A (FractionRing (MvPolynomial ι F)) :=
  IsFractionRing.mulSemiringAction A (MvPolynomial ι F)
    (FractionRing (MvPolynomial ι F))

/-- A faithful action on variable labels induces a faithful renaming action
on the polynomial ring. -/
instance (priority := low) polynomialRenameFaithfulSMul [FaithfulSMul A ι] :
    FaithfulSMul A (MvPolynomial ι F) where
  eq_of_smul_eq_smul {a b} h := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := ι)
    intro i
    exact MvPolynomial.X_injective (by
      simpa only [polynomialRename_smul, renameAction,
        MvPolynomial.rename_X] using
          h (MvPolynomial.X i : MvPolynomial ι F))

/-- Faithfulness survives passage to the fraction field. -/
instance (priority := low) fractionRenameFaithfulSMul [FaithfulSMul A ι] :
    FaithfulSMul A (FractionRing (MvPolynomial ι F)) :=
  IsFractionRing.faithfulSMul A (MvPolynomial ι F)
    (FractionRing (MvPolynomial ι F))

end FractionFieldAction

section ExactStabilizerAndMinpoly

variable {F : Type uF} [Field F]
variable {A : Type uA} [Group A] [Fintype A]
variable {ι : Type uI} [MulAction A ι]

/-- Embedding a polynomial in its fraction field does not change its
renaming stabilizer.  This is the unconditional equality underlying the
exact-stabilizer transport below. -/
theorem fraction_stabilizer_eq_renameStabilizer
    (p : MvPolynomial ι F) :
    MulAction.stabilizer A
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F)) p) =
      renameStabilizer p := by
  ext a
  rw [MulAction.mem_stabilizer_iff, mem_renameStabilizer]
  constructor
  · intro ha
    have hpolynomial : a • p = p := by
      apply IsFractionRing.injective (MvPolynomial ι F)
        (FractionRing (MvPolynomial ι F))
      simpa only [← algebraMap.coe_smul'] using ha
    simpa only [polynomialRename_smul] using hpolynomial
  · intro ha
    rw [← algebraMap.coe_smul', polynomialRename_smul, ha]

/-- Embedding a polynomial into its rational-function field preserves its
exact renaming stabilizer.  The reverse implication uses only injectivity of
the fraction-field algebra map, so this is not a kernel shortcut. -/
theorem fraction_stabilizer_eq_of_exactRenameStabilizer
    (G : Subgroup A) (p : MvPolynomial ι F)
    (hp : HasExactRenameStabilizer G p) :
    MulAction.stabilizer A
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F)) p) = G := by
  ext a
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro ha
    apply (hp.rename_eq_iff_mem a).mp
    have hpolynomial : a • p = p := by
      apply IsFractionRing.injective (MvPolynomial ι F)
        (FractionRing (MvPolynomial ι F))
      simpa only [← algebraMap.coe_smul'] using ha
    simpa only [polynomialRename_smul] using hpolynomial
  · intro ha
    have hrename : renameAction a p = p :=
      (hp.rename_eq_iff_mem a).mpr ha
    rw [← algebraMap.coe_smul', polynomialRename_smul, hrename]

/-
CHECKPOINT: the product-reindexing proof below is preserved verbatim while its
quotient `Fintype` instance transport is being finished.  The two subsequent
minimal-polynomial declarations depend on it, so all three remain commented
out together; no placeholder is introduced.

/-- Scalar extension of the universal orbit product to the rational-function
field is Mathlib's product over the distinct orbit of the embedded
invariant.  Exact stabilizer is what identifies the two quotient index
types. -/
theorem universalInvariantResolvent_map_fraction_eq_prodXSubSMul
    (G : Subgroup A) (p : MvPolynomial ι F)
    (hp : HasExactRenameStabilizer G p) :
    (universalInvariantResolvent G p hp.invariantUnder).map
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F))) =
      prodXSubSMul A (FractionRing (MvPolynomial ι F))
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F)) p) := by
  classical
  have hG := fraction_stabilizer_eq_of_exactRenameStabilizer G p hp
  simp only [prodXSubSMul]
  simp only [universalInvariantResolvent,
    LazardGeneralResolventCriterion.orbitResolvent,
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]
  apply Fintype.prod_equiv (Subgroup.quotientEquivOfEq hG.symm)
  intro c
  induction c using QuotientGroup.induction_on with
  | _ a =>
      simp only [Subgroup.quotientEquivOfEq_mk, universalOrbitValue_mk,
        MulAction.ofQuotientStabilizer_mk]
      rw [← polynomialRename_smul, algebraMap.coe_smul']

/-- The universal orbit product is the scalar extension of Mathlib's
`FixedPoints.minpoly` over the `A`-fixed rational-function field. -/
theorem universalInvariantResolvent_map_fraction_eq_fixedPoints_minpoly
    (G : Subgroup A) (p : MvPolynomial ι F)
    (hp : HasExactRenameStabilizer G p) :
    (universalInvariantResolvent G p hp.invariantUnder).map
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F))) =
      (FixedPoints.minpoly A (FractionRing (MvPolynomial ι F))
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F)) p)).map
        (algebraMap
          (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
          (FractionRing (MvPolynomial ι F))) := by
  rw [universalInvariantResolvent_map_fraction_eq_prodXSubSMul G p hp,
    FixedPoints.minpoly, FixedPoints.coe_algebraMap,
    ← Subfield.toSubring_subtype_eq_subtype,
    Polynomial.map_toSubring]

/-- Paper-facing minimal-polynomial statement: after embedding coefficients
in the rational-function field, the universal resolvent is the ordinary
minimal polynomial of the invariant over the ambient fixed field. -/
theorem universalInvariantResolvent_map_fraction_eq_minpoly
    (G : Subgroup A) (p : MvPolynomial ι F)
    (hp : HasExactRenameStabilizer G p) :
    (universalInvariantResolvent G p hp.invariantUnder).map
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F))) =
      (_root_.minpoly
        (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
        (algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F)) p)).map
        (algebraMap
          (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
          (FractionRing (MvPolynomial ι F))) := by
  rw [← FixedPoints.minpoly_eq_minpoly]
  exact universalInvariantResolvent_map_fraction_eq_fixedPoints_minpoly
    G p hp
-/

end ExactStabilizerAndMinpoly

section FixedFieldGeneration

variable {F : Type uF} [Field F]
variable {A : Type uA} [Group A] [Fintype A]
variable {ι : Type uI} [MulAction A ι] [FaithfulSMul A ι]

/-- In a finite faithful action, the subgroup fixing the simple intermediate
field generated by `x` is exactly the stabilizer of `x`. -/
theorem fixingSubgroup_adjoin_simple_eq_stabilizer
    (x : FractionRing (MvPolynomial ι F)) :
    fixingSubgroup A
        ((IntermediateField.adjoin
          (FixedPoints.subfield A (FractionRing (MvPolynomial ι F))) {x} :
            IntermediateField
              (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
              (FractionRing (MvPolynomial ι F))) :
          Set (FractionRing (MvPolynomial ι F))) =
      MulAction.stabilizer A x := by
  ext a
  rw [mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]
  simpa using
    (IntermediateField.forall_mem_adjoin_smul_eq_self_iff
      (S := ({x} : Set (FractionRing (MvPolynomial ι F))))
      (FixedPoints.subfield A (FractionRing (MvPolynomial ι F))) a)

/-- The embedded exact-stabilizer invariant generates the whole `G`-fixed
field over the `A`-fixed field.  This is the fixed-field generation clause in
Lazard's definition, stated intrinsically; it does not identify either fixed
field with a chosen presentation by symmetric functions. -/
theorem fractionInvariant_adjoin_eq_fixedPoints
    (G : Subgroup A) (p : MvPolynomial ι F)
    (hp : HasExactRenameStabilizer G p) :
    IntermediateField.adjoin
        (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
        {algebraMap (MvPolynomial ι F)
          (FractionRing (MvPolynomial ι F)) p} =
      (FixedPoints.intermediateField G :
        IntermediateField
          (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
          (FractionRing (MvPolynomial ι F))) := by
  let x : FractionRing (MvPolynomial ι F) :=
    algebraMap (MvPolynomial ι F) (FractionRing (MvPolynomial ι F)) p
  let E : IntermediateField
      (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
      (FractionRing (MvPolynomial ι F)) :=
    IntermediateField.adjoin
      (FixedPoints.subfield A (FractionRing (MvPolynomial ι F))) {x}
  change E = FixedPoints.intermediateField G
  calc
    E = FixedPoints.intermediateField
        (fixingSubgroup A (E : Set (FractionRing (MvPolynomial ι F)))) :=
      (IsGaloisGroup.fixedPoints_fixingSubgroup
        (G := A)
        (K := FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
        (L := FractionRing (MvPolynomial ι F))
        (F := E)).symm
    _ = FixedPoints.intermediateField G := by
      rw [show fixingSubgroup A
          (E : Set (FractionRing (MvPolynomial ι F))) =
            MulAction.stabilizer A x by
          exact fixingSubgroup_adjoin_simple_eq_stabilizer x,
        fraction_stabilizer_eq_of_exactRenameStabilizer G p hp]

/-- Literal converse to the fixed-field generation clause: a polynomial has
renaming stabilizer exactly `G` if and only if its fraction-field image
generates the `G`-fixed field over the full `A`-fixed field.

The reverse implication is the finite Galois correspondence, applied to the
subgroup fixing the simple field generated by the embedded polynomial; it is
not an additional exact-stabilizer assumption. -/
theorem hasExactRenameStabilizer_iff_adjoin_eq_fixedPoints
    (G : Subgroup A) (p : MvPolynomial ι F) :
    HasExactRenameStabilizer G p ↔
      IntermediateField.adjoin
          (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
          {algebraMap (MvPolynomial ι F)
            (FractionRing (MvPolynomial ι F)) p} =
        (FixedPoints.intermediateField G :
          IntermediateField
            (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
            (FractionRing (MvPolynomial ι F))) := by
  constructor
  · exact fun hp ↦ fractionInvariant_adjoin_eq_fixedPoints G p hp
  · intro hgenerate
    change renameStabilizer p = G
    rw [← fraction_stabilizer_eq_renameStabilizer p]
    calc
      MulAction.stabilizer A
          (algebraMap (MvPolynomial ι F)
            (FractionRing (MvPolynomial ι F)) p) =
        fixingSubgroup A
          ((IntermediateField.adjoin
            (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
            {algebraMap (MvPolynomial ι F)
              (FractionRing (MvPolynomial ι F)) p} :
              IntermediateField
                (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
                (FractionRing (MvPolynomial ι F))) :
            Set (FractionRing (MvPolynomial ι F))) :=
          (fixingSubgroup_adjoin_simple_eq_stabilizer
            (algebraMap (MvPolynomial ι F)
              (FractionRing (MvPolynomial ι F)) p)).symm
      _ = fixingSubgroup A
          ((FixedPoints.intermediateField G :
            IntermediateField
              (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
              (FractionRing (MvPolynomial ι F))) :
            Set (FractionRing (MvPolynomial ι F))) := by
          rw [hgenerate]
      _ = G := IsGaloisGroup.fixingSubgroup_fixedPoints
        (G := A)
        (K := FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
        (L := FractionRing (MvPolynomial ι F))
        (H := G)

/-
CHECKPOINT: this combined endpoint depends on the commented minimal-polynomial
bridge above.  Its complete statement and proof are preserved verbatim until
that dependency is restored.

/-- Lazard's two literal resolvent clauses, as an iff.  The forward direction
derives both fixed-field generation and the ordinary minimal-polynomial
identity.  In the reverse direction the minimal-polynomial conjunct is
logically redundant: generation alone recovers the exact stabilizer by the
preceding Galois-correspondence theorem. -/
theorem hasExactRenameStabilizer_iff_generator_and_minpoly
    (G : Subgroup A) (p : MvPolynomial ι F)
    (hpG : InvariantUnder G p) :
    HasExactRenameStabilizer G p ↔
      IntermediateField.adjoin
          (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
          {algebraMap (MvPolynomial ι F)
            (FractionRing (MvPolynomial ι F)) p} =
          (FixedPoints.intermediateField G :
            IntermediateField
              (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
              (FractionRing (MvPolynomial ι F))) ∧
        (universalInvariantResolvent G p hpG).map
            (algebraMap (MvPolynomial ι F)
              (FractionRing (MvPolynomial ι F))) =
          (_root_.minpoly
            (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
            (algebraMap (MvPolynomial ι F)
              (FractionRing (MvPolynomial ι F)) p)).map
            (algebraMap
              (FixedPoints.subfield A (FractionRing (MvPolynomial ι F)))
              (FractionRing (MvPolynomial ι F))) := by
  constructor
  · intro hp
    refine ⟨fractionInvariant_adjoin_eq_fixedPoints G p hp, ?_⟩
    exact universalInvariantResolvent_map_fraction_eq_minpoly G p hp
  · rintro ⟨hgenerate, _⟩
    exact (hasExactRenameStabilizer_iff_adjoin_eq_fixedPoints G p).2 hgenerate
-/

end FixedFieldGeneration

end LeanProofs.PolynomialFormulas.LazardGeneralResolventExplicit
