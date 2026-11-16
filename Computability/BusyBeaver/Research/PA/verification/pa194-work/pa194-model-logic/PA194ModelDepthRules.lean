import PA194ModelLinearSeed
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Deep linear-stack seeds and a depth-indexed partial compiler admission. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
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
local instance depthRulesZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance depthRulesOne : One M := ⟨F oneCode Fin.elim0⟩
local instance depthRulesAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance depthRulesMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance depthRulesLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance depthRulesIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]



/-- The admission part of the source shift rule, excluding the global code bound. -/
theorem depthAdmission_shift (e s d : M) (h : DepthAdmission e (shiftRule s d)) :
    DepthAdmission (simPopFree e) d :=
  depthAdmission_pop_child e _ d (d_lt_shiftRule s d) h

/-- The admission part of the source universal rule, excluding the global code bound. -/
theorem depthAdmission_all (e s p d : M) (h : DepthAdmission e (allIntro s p d)) :
    DepthAdmission (simPushFree e) d :=
  depthAdmission_push_child e _ d (s_lt_allIntro s p d) h

/-- The target shift field for an admitted environment and an explicit bridge. -/
theorem simRuleShift_of_depthBridge (e d p : M) (h : DepthAdmission e d)
    (hb : ShiftBridge p (simBound (simPopFree e)) (simFree (simPopFree e))
      (simBase (simPopFree e)) (simReserve (simPopFree e))) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (shift SourceL p))
      (numericalTranslation.tr (simPopFree e) p)) := by
  have hi := simPushFree_pop_of_linear e h.1 (depthAdmission_nonempty e d h)
  have hh := simRuleShift_of_bridge (simPopFree e) p hb
  rw [hi] at hh
  exact hh

theorem simRuleShift_depthPositiveAtom (e d r a b : M) (h : DepthAdmission e d)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (shift SourceL (^rel (2 : M) r ?[a,b])))
      (numericalTranslation.tr (simPopFree e) (^rel (2 : M) r ?[a,b]))) := by
  have hi := simPushFree_pop_of_linear e h.1 (depthAdmission_nonempty e d h)
  have hh := simRuleShift_positiveAtom (simPopFree e) r a b hr ha hb
  rw [hi] at hh
  exact hh

theorem simRuleShift_depthNegativeAtom (e d r a b : M) (h : DepthAdmission e d)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (shift SourceL (^nrel (2 : M) r ?[a,b])))
      (numericalTranslation.tr (simPopFree e) (^nrel (2 : M) r ?[a,b]))) := by
  have hi := simPushFree_pop_of_linear e h.1 (depthAdmission_nonempty e d h)
  have hh := simRuleShift_negativeAtom (simPopFree e) r a b hr ha hb
  rw [hi] at hh
  exact hh

#print axioms depthAdmission_shift
#print axioms depthAdmission_all
#print axioms simRuleShift_of_depthBridge
#print axioms simRuleShift_depthPositiveAtom
#print axioms simRuleShift_depthNegativeAtom
end models
end PA194ModelLogic
