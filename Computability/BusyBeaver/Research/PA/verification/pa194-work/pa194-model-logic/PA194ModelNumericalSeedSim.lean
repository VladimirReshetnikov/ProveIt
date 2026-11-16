import PA194ModelAdjunctiveSim

/-! General target witness and seeded existential-introduction rule. -/
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
local instance genericNumericalSimZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance genericNumericalSimOne : One M := ⟨F oneCode Fin.elim0⟩
local instance genericNumericalSimAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance genericNumericalSimMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance genericNumericalSimLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance genericNumericalSimIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def numericalSeedSim (T : Theory SourceL) [T.Δ₁]
    (reserve : M) (C : SeedCompilerAdmission 0 reserve)
    (axiomRule : ∀ e s p : M, SeedAdmission 0 reserve e (axm s p) → p ∈ T.Δ₁Class →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1)) :
    ConPA.Sequent.ShiftValidity.Sim (numericalQuant (M := M)) numericalTranslation T := by
  refine {
    bot := 1
    bound := C.limit
    Adm := SeedAdmission 0 reserve
    adm_definable := seedAdmission_definable 0 reserve
    push := simPushFree
    pop := simPopFree
    eig := simBase
    admAnd := ?_
    admOr := ?_
    admAll := ?_
    admExs := ?_
    admWk := ?_
    admShift := ?_
    admCut := ?_
    ruleAxL := ?_
    ruleVerum := ?_
    ruleAnd := ?_
    ruleOr := ?_
    ruleAllShift := ?_
    ruleAllFresh := ?_
    ruleAll := ?_
    ruleExs := ?_
    ruleShift := ?_
    ruleCut := ?_
    ruleAxm := ?_ }
  · intro e s p q dp dq h
    exact C.andRule e s p q dp dq h
  · intro e s p q d h
    exact C.orRule e s p q d h
  · intro e s p d h
    exact C.allRule e s p d h
  · intro e s p t d h
    exact C.exRule e s p t d h
  · intro e s d h
    exact C.wkRule e s d h
  · intro e s d h
    exact C.shiftRule e s d h
  · intro e s p d₁ d₂ h
    exact C.cutRule e s p d₁ d₂ h
  · intro e s p _ _ hs hp _
    exact simRuleAxL e s p hs hp
  · intro e s _ _ _ _
    exact simRuleVerum e
  · intro e s p q dp dq _ _ hs hm
    exact simRuleAnd e s p q hs hm
  · intro e s p q d _ _ hs hm
    exact simRuleOr e s p q hs hm
  · intro e s p d _ ha hs hm q hq
    exact simRuleAllShift_generalSeed reserve e s p q d ha hs hm hq
  · intro e s p d _ ha hs hm q hq
    exact simRuleAllFresh_generalSeed reserve e s p q d ha hs hm hq
  · intro e s p d _ _ hs hm
    exact simRuleAll_general e s p hs hm
  · intro e s p t d _ ha hs hm ht
    exact simRuleExs_generalSeed reserve e s p t d ha hs hm ht
  · intro e d _ ha hs q hq
    exact simRuleShift_generalSeed_set reserve e d q ha hs hq
  · intro e s p d₁ d₂ _ _ _ hp
    exact simRuleCut_valid e p hp
  · intro e s p _ ha _ _ hT
    exact axiomRule e s p ha hT


#print axioms numericalSeedSim
end models
end PA194ModelLogic
