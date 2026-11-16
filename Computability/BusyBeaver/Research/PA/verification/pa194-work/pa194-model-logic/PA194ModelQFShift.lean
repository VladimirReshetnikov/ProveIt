import PA194ModelSourceShiftAtom
import PA194ModelDepthRules
import PA194ModelQuantifierFreeFresh
import PA194ModelSafeQF
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal structural induction for arbitrary-label vacuity. -/
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
local instance qfShiftUniformZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfShiftUniformOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfShiftUniformAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfShiftUniformMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfShiftUniformLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfShiftUniformIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Uniform source-shift/translation agreement for arbitrary internal
quantifier-free formula codes. -/
theorem quantifierFree_shiftBridge (p bound freeEnv base reserve : M)
    (hp : IsUFormula SourceL p) (hqf : InternalQuantifierFree p) :
    ShiftBridge p bound freeEnv base reserve := by
  let e := pair bound (pair freeEnv (pair base reserve))
  let e' := pair bound (pair (pair base freeEnv+1) (pair (base+1) reserve))
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  haveI : 𝚺₁-Function₁ (shift SourceL : M → M) := shift.definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q →
      positiveTranslation e' (shift SourceL q) = positiveTranslation e q) := by definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q →
      positiveTranslation e' (shift SourceL q) = positiveTranslation e q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv _
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact shift_positiveAtom_translation r a b bound freeEnv base reserve hr ha hb
    · intro arity r v hr hv _
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact shift_negativeAtom_translation r a b bound freeEnv base reserve hr ha hb
    · intro _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,shift_verum,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,shift_falsum,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
    · intro a b ha hb iha ihb hfree
      have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree)
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree)
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [shift_and ha hb,fixedFormulaTranslation_and _ _ _ _ _ _ ha.shift hb.shift,
        fixedFormulaTranslation_and _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a b ha hb iha ihb hfree
      have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree)
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree)
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [shift_or ha hb,fixedFormulaTranslation_or _ _ _ _ _ _ ha.shift hb.shift,
        fixedFormulaTranslation_or _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a ha ih hfree
      exact False.elim (internalQuantifierFree_not_all a hfree)
    · intro a ha ih hfree
      exact False.elim (internalQuantifierFree_not_ex a hfree)
  have hh := hall p hp hqf
  dsimp only [e,e'] at hh
  simpa only [positiveTranslation_model,ShiftBridge] using hh

theorem simRuleAllShift_quantifierFree (e p : M)
    (hp : IsUFormula SourceL p) (hqf : InternalQuantifierFree p) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p)
      (numericalTranslation.tr (simPushFree e) (shift SourceL p))) :=
  simRuleAllShift_of_bridge e p
    (quantifierFree_shiftBridge p (simBound e) (simFree e) (simBase e) (simReserve e) hp hqf)

theorem simRuleShift_quantifierFree (e d p : M) (ha : DepthAdmission e d)
    (hp : IsUFormula SourceL p) (hqf : InternalQuantifierFree p) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (shift SourceL p))
      (numericalTranslation.tr (simPopFree e) p)) :=
  simRuleShift_of_depthBridge e d p ha
    (quantifierFree_shiftBridge p (simBound (simPopFree e)) (simFree (simPopFree e))
      (simBase (simPopFree e)) (simReserve (simPopFree e)) hp hqf)

#print axioms quantifierFree_shiftBridge
#print axioms simRuleAllShift_quantifierFree
#print axioms simRuleShift_quantifierFree
end models
end PA194ModelLogic
