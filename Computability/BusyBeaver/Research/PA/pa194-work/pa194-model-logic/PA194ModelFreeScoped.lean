import PA194ModelFreeTerm
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
local instance freeScopedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeScopedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeScopedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeScopedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeScopedLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeScopedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem simRuleAll_wellScopedPositiveAtom (e s r a b : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s)
    (hm : (^∀ (^rel (2 : M) r ?[a,b])) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e)
          (LO.FirstOrder.Arithmetic.Bootstrapping.free M6.PA.RelationalSource.language (^rel (2 : M) r ?[a,b]))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^rel (2 : M) r ?[a,b]))) 1)) := by
  have hf : IsFormula M6.PA.RelationalSource.language (^∀ (^rel (2 : M) r ?[a,b])) := hs _ hm
  have hbody : IsSemiformula M6.PA.RelationalSource.language 1 (^rel (2 : M) r ?[a,b]) := by
    simpa only [IsSemiformula.all,zero_add] using hf
  have hparts := IsSemiformula.rel.mp hbody
  obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp hparts.2
  exact simRuleAll_positiveAtom e s r a b hs hm hparts.1 ha hb

theorem simRuleAll_wellScopedNegativeAtom (e s r a b : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s)
    (hm : (^∀ (^nrel (2 : M) r ?[a,b])) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e)
          (LO.FirstOrder.Arithmetic.Bootstrapping.free M6.PA.RelationalSource.language (^nrel (2 : M) r ?[a,b]))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^nrel (2 : M) r ?[a,b]))) 1)) := by
  have hf : IsFormula M6.PA.RelationalSource.language (^∀ (^nrel (2 : M) r ?[a,b])) := hs _ hm
  have hbody : IsSemiformula M6.PA.RelationalSource.language 1 (^nrel (2 : M) r ?[a,b]) := by
    simpa only [IsSemiformula.all,zero_add] using hf
  have hparts := IsSemiformula.nrel.mp hbody
  obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp hparts.2
  exact simRuleAll_negativeAtom e s r a b hs hm hparts.1 ha hb

#print axioms simRuleAll_wellScopedPositiveAtom
#print axioms simRuleAll_wellScopedNegativeAtom
end models
end PA194ModelLogic
