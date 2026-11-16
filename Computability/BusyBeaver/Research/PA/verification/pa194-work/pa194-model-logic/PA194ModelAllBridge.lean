import PA194ModelFreeBoolean
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance allBridgeZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance allBridgeOne : One M := ⟨F oneCode Fin.elim0⟩
local instance allBridgeAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance allBridgeMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance allBridgeLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance allBridgeIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem simRuleAll_of_bridge (e s p : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s)
    (h : FreeBridge p (simBound e) (simFree e) (simBase e) (simReserve e)) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p)) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ p)) 1)) := by
  apply simRuleAll_of_freeBridge e s p hs hm
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  unfold FreeBridge at h
  simpa only [hbound,hfree,hbase,hreserve] using h

theorem simRuleAll_verum (e s : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ (^⊤ : M)) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (^⊤))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^⊤ : M))) 1)) :=
  simRuleAll_of_bridge e s (^⊤) hs hm (freeBridge_verum _ _ _ _)

theorem simRuleAll_falsum (e s : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ (^⊥ : M)) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (^⊥))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^⊥ : M))) 1)) :=
  simRuleAll_of_bridge e s (^⊥) hs hm (freeBridge_falsum _ _ _ _)

#print axioms simRuleAll_of_bridge
#print axioms simRuleAll_verum
#print axioms simRuleAll_falsum
end models
end PA194ModelLogic
