import PA194IntersectionMember
import PA194IntersectionTyped
import PA194TypedSchema
import PA194SourceIntersection
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalSuppliers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ReopenProof PA194TypedSchema PA194FullSepOpen PA194IntersectionMember PA194TypedSeparation
open M6.PA.RelationalSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundClosedLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundClosedLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundClosedLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundClosedLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundClosedLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundClosedLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem negated_property_separation_provable (p : M)
    (hp : IsSemiformula SourceL 1 p) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (sepRoot (neg SourceL p)) := by
  exact adjunctive_full_sep_root_provable (neg SourceL p) hp.neg

theorem typed_negated_property_separation_provable
    (p : Semiproposition M6.PA.RelationalSource.language 1) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (⌜separationFormula (∼p)⌝ : M) := by
  letI := adjunctiveFullSepTheoryDelta
  have h := negated_property_separation_provable (⌜p⌝ : M) (Semiformula.quote_isSemiformul₁ p)
  rw [← quote_neg, ← separationFormula_quote] at h
  exact h

theorem ordinal_source_suppliers (p : M)
    (hp : IsSemiformula SourceL 1 p) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (⌜Ordinal.intersectionFormula⌝ : M) ∧
      Provable adjunctiveFullSepTheory (sepRoot (neg SourceL p)) := by
  exact ⟨intersection_provable, negated_property_separation_provable p hp⟩

#print axioms negated_property_separation_provable
#print axioms typed_negated_property_separation_provable
#print axioms ordinal_source_suppliers
end models
end PA194OrdinalSuppliers
