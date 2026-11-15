import PA194ReopenProof
import PA194AdjunctiveFullSep
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194FullSepOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ReopenProof
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

theorem full_sep_root_provable (p : M)
    (hp : IsSemiformula SourceL 1 p) :
    letI := fullSepTheoryDelta
    Provable fullSepTheory (sepRoot p) := by
  letI := fullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨fullSepTheory, fullSepTheoryDelta⟩
  have ha : fullyClosedSeparation p ∈ fullSepTheory.Δ₁Class (V := M) :=
    (fullSepTheory_class _).2 ⟨p,hp,rfl⟩
  exact separation_root_provable T p hp ha

theorem adjunctive_full_sep_root_provable (p : M)
    (hp : IsSemiformula SourceL 1 p) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (sepRoot p) := by
  letI := adjunctiveFullSepTheoryDelta
  letI := adjunctiveTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  have ha : fullyClosedSeparation p ∈ adjunctiveFullSepTheory.Δ₁Class (V := M) :=
    (adjunctiveFullSepTheory_class _).2 (Or.inr ⟨p,hp,rfl⟩)
  exact separation_root_provable T p hp ha

#print axioms full_sep_root_provable
#print axioms adjunctive_full_sep_root_provable
end models
end PA194FullSepOpen
