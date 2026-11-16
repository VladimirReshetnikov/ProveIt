import PA194ModelQFSubstitution
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
local instance qfTailZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfTailOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfTailAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfTailMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfTailLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfTailIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- A one-variable source atom does not inspect the tail of its bound stack. -/
theorem positiveAtom_boundTail (r a b c tail₁ tail₂ free reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],pair c tail₁+1,free,c+1,reserve] =
      F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],pair c tail₂+1,free,c+1,reserve] := by
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
      · rw [fixedTranslation_equalityBoundDiagonal,fixedTranslation_equalityBoundDiagonal]
      · rw [fixedTranslation_equalityBoundLeft,fixedTranslation_equalityBoundLeft]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
      · rw [fixedTranslation_equalityBoundRight,fixedTranslation_equalityBoundRight]
      · rw [fixedTranslation_equalityFree,fixedTranslation_equalityFree]
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
      · rw [fixedTranslation_membershipBoundDiagonal,fixedTranslation_membershipBoundDiagonal]
      · rw [fixedTranslation_membershipBoundLeft,fixedTranslation_membershipBoundLeft]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
      · rw [fixedTranslation_membershipBoundRight,fixedTranslation_membershipBoundRight]
      · rw [fixedTranslation_membershipFree,fixedTranslation_membershipFree]

theorem negativeAtom_boundTail (r a b c tail₁ tail₂ free reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],pair c tail₁+1,free,c+1,reserve] =
      F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],pair c tail₂+1,free,c+1,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv]
  exact congrArg negValue (positiveAtom_boundTail r a b c tail₁ tail₂ free reserve hr ha hb)

theorem quantifierFree_boundTail (p c tail₁ tail₂ free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p) :
    F fixedFormulaTranslation ![p,pair c tail₁+1,free,c+1,reserve] =
      F fixedFormulaTranslation ![p,pair c tail₂+1,free,c+1,reserve] := by
  let e := pair (pair c tail₁+1) (pair free (pair (c+1) reserve))
  let e' := pair (pair c tail₂+1) (pair free (pair (c+1) reserve))
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q → IsSemiformula SourceL 1 q →
      positiveTranslation e q = positiveTranslation e' q) := by definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q → IsSemiformula SourceL 1 q →
      positiveTranslation e q = positiveTranslation e' q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv _ hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact positiveAtom_boundTail r a b c tail₁ tail₂ free reserve hr ha hb
    · intro arity r v hr hv _ hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact negativeAtom_boundTail r a b c tail₁ tail₂ free reserve hr ha hb
    · intro _ _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro _ _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
    · intro a b ha hb iha ihb hfree hscope
      have hleft : SourceDirectEdge (a ^⋏ b) a 0 := by
        left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋏ b) b 0 := by
        left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hscope
      have ih1 := iha (internalQuantifierFree_child _ _ _ hleft hfree) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hright hfree) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_and a b _ _ _ _ ha hb,
        fixedFormulaTranslation_and a b _ _ _ _ ha hb,ih1,ih2]
    · intro a b ha hb iha ihb hfree hscope
      have hleft : SourceDirectEdge (a ^⋎ b) a 0 := by
        right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋎ b) b 0 := by
        right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ih1 := iha (internalQuantifierFree_child _ _ _ hleft hfree) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hright hfree) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_or a b _ _ _ _ ha hb,
        fixedFormulaTranslation_or a b _ _ _ _ ha hb,ih1,ih2]
    · intro a ha ih hfree hscope
      exact False.elim (internalQuantifierFree_not_all a hfree)
    · intro a ha ih hfree hscope
      exact False.elim (internalQuantifierFree_not_ex a hfree)
  have hh := hall p hp.isUFormula hqf hp
  dsimp only [e,e'] at hh
  simpa only [positiveTranslation_model] using hh



/-- Exact existential-rule field for arbitrary quantifier-free bodies under
ranked admission, with no restriction on the bound-stack tail. -/
theorem simRuleExs_quantifierFreeRankedFull (e s p t d : M)
    (ha : RankedAdmission e (exsIntro s p t d))
    (hs : IsFormulaSet SourceL s) (hm : (^∃ p) ∈ s) (ht : IsTerm SourceL t)
    (hqf : InternalQuantifierFree p) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t p)) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ p)) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  have hbody : IsSemiformula SourceL 1 p := by
    have hf := hs _ hm
    simpa only [IsSemiformula.exs,zero_add] using hf
  have hcx : (simFree e).[j] < simBase e := rankedEnvironment_free_lt e j ha.1
  have hfree : ∀ i : M, (simFree e).[i] < simBase e := fun i => rankedEnvironment_free_lt e i ha.1
  have hxz : simBase e < simReserve e :=
    partialAdmission_base_lt_reserve 0 e _ (rankedAdmission_to_partial 0 e _ ha)
  apply simRuleExs_of_intro e s p (^&j) hs hm (by simp)
  rw [fixedFormulaTranslation_ex _ _ _ _ _ hbody.isUFormula]
  rw [(quantifierFree_substitution_translation p j (simBound e) (simFree e) (simBase e) (simReserve e) hbody hqf).2]
  rw [quantifierFree_boundTail p (simFree e).[j] (simBound e) 0 (simFree e) (simReserve e) hbody hqf,
    quantifierFree_boundTail p (simBase e) (simBound e) 0 (simFree e) (simReserve e) hbody hqf]
  exact targetExistsQF_freeWitness p (simBase e) (simFree e).[j] (simFree e) (simReserve e)
    hbody hqf hcx hfree hxz

#print axioms simRuleExs_quantifierFreeRankedFull
#print axioms quantifierFree_boundTail
#print axioms positiveAtom_boundTail
#print axioms negativeAtom_boundTail
end models
end PA194ModelLogic
