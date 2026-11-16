import PA194ModelAllBridge
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
local instance qfFreeUniformZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfFreeUniformOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfFreeUniformAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfFreeUniformMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfFreeUniformLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfFreeUniformIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Uniform source-freeing/translation agreement for arbitrary internal
quantifier-free one-bound-variable formula codes. -/
theorem quantifierFree_freeBridge (p bound freeEnv base reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p) :
    FreeBridge p bound freeEnv base reserve := by
  let e := pair (pair base bound+1) (pair freeEnv (pair (base+1) reserve))
  let e' := pair bound (pair (pair base freeEnv+1) (pair (base+1) reserve))
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  haveI : 𝚺₁-Function₁ (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL : M → M) := by
    unfold LO.FirstOrder.Arithmetic.Bootstrapping.free substs1
    definability
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q → IsSemiformula SourceL 1 q →
      positiveTranslation e' (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL q) = positiveTranslation e q) := by definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q → IsSemiformula SourceL 1 q →
      positiveTranslation e' (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL q) = positiveTranslation e q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv _ hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact free_positiveAtom_translation r a b bound freeEnv base reserve hr hsa hsb
    · intro arity r v hr hv _ hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact free_negativeAtom_translation r a b bound freeEnv base reserve hr hsa hsb
    · intro _ _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact freeBridge_verum bound freeEnv base reserve
    · intro _ _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact freeBridge_falsum bound freeEnv base reserve
    · intro a b ha hb iha ihb hfree hscope
      have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hscope
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      exact freeBridge_and a b bound freeEnv base reserve hsa hsb ih1 ih2
    · intro a b ha hb iha ihb hfree hscope
      have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      exact freeBridge_or a b bound freeEnv base reserve hsa hsb ih1 ih2
    · intro a ha ih hfree hscope
      exact False.elim (internalQuantifierFree_not_all a hfree)
    · intro a ha ih hfree hscope
      exact False.elim (internalQuantifierFree_not_ex a hfree)
  have hh := hall p hp.isUFormula hqf hp
  dsimp only [e,e'] at hh
  simpa only [positiveTranslation_model,FreeBridge] using hh

theorem simRuleAll_quantifierFree (e s p : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s) (hqf : InternalQuantifierFree p) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p)) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ p)) 1)) := by
  have hp : IsSemiformula SourceL 1 p := by
    have h := hs _ hm
    simpa only [IsSemiformula.all,zero_add] using h
  exact simRuleAll_of_bridge e s p hs hm
    (quantifierFree_freeBridge p (simBound e) (simFree e) (simBase e) (simReserve e) hp hqf)

#print axioms quantifierFree_freeBridge
#print axioms simRuleAll_quantifierFree
end models
end PA194ModelLogic
