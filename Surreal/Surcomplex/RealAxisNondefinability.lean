import Surreal.Algebra.DefinabilityAutomorphisms
import Surreal.Surcomplex.PhaseTwist
import Mathlib.ModelTheory.Algebra.Ring.Basic

/-!
# No definable real axis, conjugation or real omnific subring

The full first-order assertions of `odg:def:thm:norealaxis`, using Mathlib's
native parameter-set definability. The field structure is the ring language
with one unary predicate interpreted as the actual Gaussian omnific image.
-/

universe u
namespace Surreal.Surcomplex
open Foundations FirstOrder FirstOrder.Language
noncomputable section

/-- The one extra relation symbol names the Gaussian omnific ring. -/
inductive GaussianPredicateSymbol : ℕ → Type
  | gaussian : GaussianPredicateSymbol 1

/-- The language of rings with a unary predicate for Gaussian omnific integers. -/
def gaussianPairLanguage : Language where
  Functions := Language.ring.Functions
  Relations := GaussianPredicateSymbol

/-- The field predicate is the image of the existing actual Gaussian omnific inclusion. -/
def gaussianOmnificImage : Set Surcomplex.{u} := Set.range gaussianOmnificToSurcomplex

/-- The distinguished actual real axis in the surcomplex field. -/
def realAxis : Set Surcomplex.{u} := Set.range ofReal

/-- All ordinary complex constants are allowed as parameters simultaneously. -/
def complexParameters : Set Surcomplex.{u} := Set.range ofComplex

local instance surcomplexLogicalRingStructure : FirstOrder.Ring.CompatibleRing Surcomplex.{u} :=
  FirstOrder.Ring.compatibleRingOfRing Surcomplex

/-- Ring operations and the actual Gaussian omnific predicate give the manuscript's structure. -/
instance gaussianPairStructure : gaussianPairLanguage.Structure Surcomplex.{u} where
  funMap := fun f x => FirstOrder.Language.Structure.funMap (L := Language.ring) f x
  RelMap := fun r x => match r with
    | .gaussian => x 0 ∈ gaussianOmnificImage

/-- The phase twist preserves and reflects the named Gaussian omnific predicate. -/
theorem phaseTwist_gaussianOmnificImage (z : Surcomplex.{u}) :
    phaseTwist z ∈ gaussianOmnificImage ↔ z ∈ gaussianOmnificImage := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨gaussianPhaseTwist.symm a, ?_⟩
    apply phaseTwist.injective
    rw [← gaussianPhaseTwist_value, RingEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a, rfl⟩
    exact ⟨gaussianPhaseTwist a, gaussianPhaseTwist_value a⟩

/-- The algebraic phase twist is an automorphism of the full field-and-predicate structure. -/
def phaseTwistLanguageEquiv : Surcomplex.{u} ≃[gaussianPairLanguage] Surcomplex.{u} where
  toEquiv := phaseTwist.toEquiv
  map_fun' f x := (FirstOrder.Ring.languageEquivEquivRingEquiv.symm phaseTwist).map_fun f x
  map_rel' r x := by
    cases r
    exact phaseTwist_gaussianOmnificImage (x 0)

theorem phaseTwistLanguageEquiv_fixes_parameters :
    ∀ a ∈ complexParameters.{u}, phaseTwistLanguageEquiv a = a := by
  rintro a ⟨c, rfl⟩
  exact phaseTwist_ofComplex c

/-- No first-order formula defines the actual real axis, even using arbitrary ordinary complex parameters. -/
theorem realAxis_not_definable : ¬ complexParameters.{u}.Definable₁ gaussianPairLanguage realAxis := by
  apply DefinabilityAutomorphisms.not_definable₁ phaseTwistLanguageEquiv
    phaseTwistLanguageEquiv_fixes_parameters (x := ofReal (SignSequence.omegaPower 1))
  · exact ⟨SignSequence.omegaPower 1, rfl⟩
  · rintro ⟨a, ha⟩
    exact phaseTwist_omega_not_real ⟨a, ha.symm⟩

/-- Actual conjugation has no definable graph in the same parameter-rich structure. -/
theorem conjugation_not_definable :
    ¬ complexParameters.{u}.Definable₂ gaussianPairLanguage
      {p : Surcomplex.{u} × Surcomplex.{u} | p.2 = conj p.1} := by
  apply DefinabilityAutomorphisms.not_definable₂_graph phaseTwistLanguageEquiv
    phaseTwistLanguageEquiv_fixes_parameters
  exact phaseTwist_conjugation_omega

/-- Equivalent formulation with every ordinary complex number explicitly named by a constant symbol. -/
theorem realAxis_not_definable_with_all_complex_constants :
    ¬ (∅ : Set Surcomplex.{u}).Definable₁ (gaussianPairLanguage[[complexParameters.{u}]]) realAxis := by
  change ¬ (∅ : Set Surcomplex.{u}).Definable (gaussianPairLanguage[[complexParameters.{u}]]) _
  rw [← Set.definable_iff_empty_definable_with_params]
  exact realAxis_not_definable

/-- Naming every complex constant likewise cannot make conjugation definable. -/
theorem conjugation_not_definable_with_all_complex_constants :
    ¬ (∅ : Set Surcomplex.{u}).Definable₂ (gaussianPairLanguage[[complexParameters.{u}]])
      {p : Surcomplex.{u} × Surcomplex.{u} | p.2 = conj p.1} := by
  change ¬ (∅ : Set Surcomplex.{u}).Definable (gaussianPairLanguage[[complexParameters.{u}]]) _
  rw [← Set.definable_iff_empty_definable_with_params]
  exact conjugation_not_definable

local instance gaussianLogicalRingStructure : FirstOrder.Ring.CompatibleRing GaussianOmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing GaussianOmnificInteger

/-- The ordinary Gaussian integer parameter set inside the Gaussian omnific ring. -/
def gaussianParameters : Set GaussianOmnificInteger.{u} := Set.range gaussianOmnificConstants

/-- The actual real omnific integers, viewed as a subset of Gaussian omnific integers. -/
def realOmnificImage : Set GaussianOmnificInteger.{u} :=
  {z | ∃ a : SignSequence.OmnificInteger.{u},
    gaussianOmnificToSurcomplex z = ofReal (SignSequence.omnificToSurreal a)}

/-- The phase twist is also a first-order automorphism of the pure Gaussian omnific ring. -/
def gaussianPhaseTwistLanguageEquiv :
    GaussianOmnificInteger.{u} ≃[Language.ring] GaussianOmnificInteger.{u} :=
  FirstOrder.Ring.languageEquivEquivRingEquiv.symm gaussianPhaseTwist

theorem gaussianPhaseTwistLanguageEquiv_fixes_parameters :
    ∀ a ∈ gaussianParameters.{u}, gaussianPhaseTwistLanguageEquiv a = a := by
  rintro a ⟨c, rfl⟩
  exact gaussianPhaseTwist_constants c

/-- The real omnific subring is not first-order definable in the pure Gaussian omnific ring,
even allowing parameters from every ordinary Gaussian integer. -/
theorem realOmnificImage_not_definable :
    ¬ gaussianParameters.{u}.Definable₁ Language.ring realOmnificImage := by
  apply DefinabilityAutomorphisms.not_definable₁ gaussianPhaseTwistLanguageEquiv
    gaussianPhaseTwistLanguageEquiv_fixes_parameters (x := gaussianOmnificOmega)
  · exact ⟨SignSequence.omnificMonomial 1 zero_lt_one, rfl⟩
  · exact gaussianPhaseTwist_omega_not_omnific

end
end Surreal.Surcomplex
