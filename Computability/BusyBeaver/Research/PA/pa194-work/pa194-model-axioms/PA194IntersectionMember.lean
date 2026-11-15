import PA194TypedSepMember
import PA194IntersectionTyped
import PA194TypedSchema
import PA194SourceIntersection
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IntersectionMember
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ReopenProof PA194TypedSchema
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

theorem quote_univCl_eq_self (p : Proposition M6.PA.RelationalSource.language)
    (hp : p.freeVariables = ∅) : (⌜p.univCl⌝ : M) = (⌜p⌝ : M) := by
  rw [Sentence.quote_def, Semiformula.coe_univCl_eq_univCl', Semiformula.univCl'_eq_self_of _ hp]

theorem intersection_axiom_member :
    letI := adjunctiveFullSepTheoryDelta
    (⌜Ordinal.intersectionFormula⌝ : M) ∈ adjunctiveFullSepTheory.Δ₁Class := by
  letI := adjunctiveFullSepTheoryDelta
  have h := PA194IntersectionProof.typed_separation_axiom_member (M := M) (Ordinal.intersectionProperty (.fvar 0))
  rw [intersection_typed_separation, quote_univCl_eq_self _ (by decide)] at h
  exact h

theorem provable_of_internal_axiom (q : M) (hq : IsSemiformula SourceL 0 q)
    (ha : letI := adjunctiveFullSepTheoryDelta; q ∈ adjunctiveFullSepTheory.Δ₁Class) :
    letI := adjunctiveFullSepTheoryDelta; Provable adjunctiveFullSepTheory q := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  let f : Formula M SourceL := ⟨q, hq⟩
  have hp : T ⊢ f := ⟨TProof.byAxm ha⟩
  exact TProvable.iff_provable.mp hp

theorem intersection_provable :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (⌜Ordinal.intersectionFormula⌝ : M) := by
  letI := adjunctiveFullSepTheoryDelta
  exact provable_of_internal_axiom _ (Semiformula.quote_isSemiformula₀ _) intersection_axiom_member

#print axioms intersection_axiom_member
#print axioms intersection_provable
end models
end PA194IntersectionMember
