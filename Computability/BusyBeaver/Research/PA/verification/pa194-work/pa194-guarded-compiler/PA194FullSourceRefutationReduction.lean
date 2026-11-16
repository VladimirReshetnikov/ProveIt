import PA194RemainingFixedSupplier
import PA194OrdinalInductionLink
import PA194NameFactsProof
import PA194NameVariableFull
import PA194GuardedInterpretationReductionFour

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace PA194FullSourceRefutationReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194BindSource PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage
  PRATheory PRAAddOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance ordinalFixedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalFixedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalFixedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalFixedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalFixedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalFixedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194GuardedCompiler PA194Schematic
attribute [local instance] adjunctiveFullSepTheoryDelta PA194PAeqBind.ordinaryPAeq_delta

/-- Transport an internally coded ordinary PA refutation to the full source theory,
conditional on the fixed source facts and the two source recursion clauses. -/
theorem refutation_of_source_facts
    (S : SourceFacts (V := M) adjunctiveFullSepTheory)
    (hA3 : adjunctiveFullSepTheory.internalize M ⊢ tHyp sA3)
    (hM3 : adjunctiveFullSepTheory.internalize M ⊢ tHyp sM3)
    {d : M} (hd : Proof PA194PAeq.ordinaryPAeq d (^⊥ : M)) :
    Provable adjunctiveFullSepTheory (^⊥ : M) :=
  let facts := termFacts_of_sourceFacts S (fun i => by
    rw [← singleton_eq_insert]
    exact fullSource_eVar i)
  PA194GuardedInterpretationReductionFour.refutation_of_remaining facts
    (remaining_fixed_supplier S (PA194SourceInhabited.inhabited_provable (M := M)) hA3 hM3)
    (PA194OrdinalInductionLink.induction_supplier_fullSource facts S) hd

#print axioms refutation_of_source_facts
end models
end PA194FullSourceRefutationReduction
