module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaFreeSupportBlueprint
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language
attribute [local irreducible] NumericPAeqTerm.freeBoundVecGraph
namespace FreeBound
noncomputable def construction : UformulaRec1.Construction V (blueprint) where
  rel {_} := fun k _ v ↦ listMax (NumericPAeqTerm.freeBoundVec k v)
  nrel {_} := fun k _ v ↦ listMax (NumericPAeqTerm.freeBoundVec k v)
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  all {_} := fun _ ys ↦ ys.[0]
  exs {_} := fun _ ys ↦ ys.[0]
  rel_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [NumericPAeqTerm.freeBoundVec_defined.df]
  nrel_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [NumericPAeqTerm.freeBoundVec_defined.df]
  verum_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp
  falsum_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp
  and_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp
  or_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp
  all_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp
  exs_defined := .mk fun v ↦ by
    simp only [blueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp

end FreeBound
#print axioms FreeBound.construction
end M6.PA.NumericPAeqFormula

