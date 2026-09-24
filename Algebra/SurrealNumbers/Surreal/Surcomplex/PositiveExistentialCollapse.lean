import Surreal.Algebra.PositiveExistentialDefinability
import Surreal.Foundations.OmnificDefinabilityObstructions
import Surreal.Surcomplex.DiophantineConstantsBoundary

/-!
# Positive-existential collapse on the actual omnific carriers

The actual real and Gaussian instances of `odg:def:thm:collapse`.
All ordinary integer or Gaussian integer parameters are allowed; witnesses
range over the entire actual ring at each universe.
-/

universe u v
namespace Surreal
open FirstOrder FirstOrder.Language
noncomputable section

namespace Foundations.SignSequence
local instance collapseOmnificStructure : FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- The existing actual-carrier predicate is the general fixed-parameter definition. -/
theorem omnificPositiveExistentialDefinable_iff {σ : Type v}
    (D : Set (σ → OmnificInteger.{u})) :
    OmnificPositiveExistentialDefinable D ↔
      PositiveExistentialDefinable Language.ring omnificIntCast D := Iff.rfl

/-- No such definition can contain a purely infinite omnific element while excluding zero. -/
theorem omnific_not_positiveExistentialDefinable_of_purelyInfinite
    {D : Set OmnificInteger.{u}} {x : OmnificInteger.{u}}
    (hx : x ∈ D) (hpi : x ∈ omnificPurelyInfiniteIdeal) (hzero : (0 : OmnificInteger.{u}) ∉ D) :
    ¬ OmnificPositiveExistentialDefinable {v : Fin 1 → OmnificInteger.{u} | v 0 ∈ D} :=
  not_positiveExistentialDefinable_of_retraction omnificConstantCoeff omnificIntCast
    omnificConstantCoeff_intCast hx hpi hzero

/-- Ordinary integer parameters cannot positively define the nonconstant omnific elements. -/
theorem omnific_nonconstant_not_positiveExistentialDefinable :
    ¬ OmnificPositiveExistentialDefinable
      {v : Fin 1 → OmnificInteger.{u} | v 0 ∉ Set.range omnificIntCast} := by
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw : w ∈ omnificPurelyInfiniteIdeal := omnificMonomial_mem_purelyInfinite _ _
  have hc : w ∉ Set.range omnificIntCast :=
    retraction_kernel_not_mem_range omnificConstantCoeff omnificIntCast
      omnificConstantCoeff_intCast (omnificMonomial_ne_zero _ _) hw
  exact omnific_not_positiveExistentialDefinable_of_purelyInfinite
    (D := {x | x ∉ Set.range omnificIntCast}) hc hw (fun h => h ⟨0, map_zero _⟩)

/-- Removing zero from the actual purely infinite ideal destroys positive-existential definability. -/
theorem omnific_puncturedIdeal_not_positiveExistentialDefinable :
    ¬ OmnificPositiveExistentialDefinable
      {v : Fin 1 → OmnificInteger.{u} | v 0 ∈ omnificPurelyInfiniteIdeal ∧ v 0 ≠ 0} := by
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw : w ∈ omnificPurelyInfiniteIdeal := omnificMonomial_mem_purelyInfinite _ _
  exact omnific_not_positiveExistentialDefinable_of_purelyInfinite
    (D := {x | x ∈ omnificPurelyInfiniteIdeal ∧ x ≠ 0})
    ⟨hw, omnificMonomial_ne_zero _ _⟩ hw (by simp)

end Foundations.SignSequence
namespace Surcomplex
local instance collapseGaussianStructure : FirstOrder.Ring.CompatibleRing GaussianOmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing GaussianOmnificInteger

/-- Positive-existential definability with every ordinary Gaussian integer available as a parameter. -/
abbrev GaussianOmnificPositiveExistentialDefinable {σ : Type v}
    (D : Set (σ → GaussianOmnificInteger.{u})) : Prop :=
  PositiveExistentialDefinable Language.ring gaussianOmnificConstants D

/-- Gaussian constant extraction gives the same obstruction on the actual Gaussian omnific ring. -/
theorem gaussianOmnific_not_positiveExistentialDefinable_of_purelyInfinite
    {D : Set GaussianOmnificInteger.{u}} {x : GaussianOmnificInteger.{u}}
    (hx : x ∈ D) (hpi : gaussianOmnificConstantCoeff x = 0)
    (hzero : (0 : GaussianOmnificInteger.{u}) ∉ D) :
    ¬ GaussianOmnificPositiveExistentialDefinable
      {v : Fin 1 → GaussianOmnificInteger.{u} | v 0 ∈ D} :=
  not_positiveExistentialDefinable_of_retraction gaussianOmnificConstantCoeff gaussianOmnificConstants
    gaussianOmnificConstantCoeff_constants hx hpi hzero

/-- The nonzero Gaussian omnific elements have no positive-existential definition over Z[i]. -/
theorem gaussianOmnific_nonzero_not_positiveExistentialDefinable :
    ¬ GaussianOmnificPositiveExistentialDefinable {v : Fin 1 → GaussianOmnificInteger.{u} | v 0 ≠ 0} :=
  gaussianOmnific_not_positiveExistentialDefinable_of_purelyInfinite (D := {x | x ≠ 0})
    gaussianOmnificOmega_ne_zero gaussianOmnificOmega_constantCoeff (by simp)

/-- The complement of the ordinary Gaussian constants has no such definition either. -/
theorem gaussianOmnific_nonconstant_not_positiveExistentialDefinable :
    ¬ GaussianOmnificPositiveExistentialDefinable
      {v : Fin 1 → GaussianOmnificInteger.{u} | v 0 ∉ Set.range gaussianOmnificConstants} := by
  have hc : gaussianOmnificOmega.{u} ∉ Set.range gaussianOmnificConstants :=
    retraction_kernel_not_mem_range gaussianOmnificConstantCoeff gaussianOmnificConstants
      gaussianOmnificConstantCoeff_constants gaussianOmnificOmega_ne_zero gaussianOmnificOmega_constantCoeff
  exact gaussianOmnific_not_positiveExistentialDefinable_of_purelyInfinite
    (D := {x | x ∉ Set.range gaussianOmnificConstants}) hc gaussianOmnificOmega_constantCoeff
    (fun h => h ⟨0, map_zero _⟩)

/-- The punctured Gaussian purely infinite ideal is likewise excluded. -/
theorem gaussianOmnific_puncturedIdeal_not_positiveExistentialDefinable :
    ¬ GaussianOmnificPositiveExistentialDefinable
      {v : Fin 1 → GaussianOmnificInteger.{u} | gaussianOmnificConstantCoeff (v 0) = 0 ∧ v 0 ≠ 0} :=
  gaussianOmnific_not_positiveExistentialDefinable_of_purelyInfinite
    (D := {x | gaussianOmnificConstantCoeff x = 0 ∧ x ≠ 0})
    ⟨gaussianOmnificOmega_constantCoeff, gaussianOmnificOmega_ne_zero⟩
    gaussianOmnificOmega_constantCoeff (by simp)

end Surcomplex
end
end Surreal
