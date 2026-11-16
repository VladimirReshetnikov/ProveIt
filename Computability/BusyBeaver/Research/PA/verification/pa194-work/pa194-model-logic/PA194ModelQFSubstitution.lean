import PA194ModelFullQF
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
local instance qfSubstZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfSubstOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfSubstAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfSubstMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfSubstLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfSubstIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Translation of a substituted source atom equals the atom translated with
its bound label replaced by the selected free-variable label. -/
theorem positiveAtom_substitution_translation (r a b j bound free base reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    F fixedFormulaTranslation ![substs1 SourceL (^&j) (^rel (2 : M) r ?[a,b]),bound,free,base,reserve] =
      F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],pair (free.[j]) bound+1,free,(free.[j])+1,reserve] := by
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_equalityBoundDiagonal, fixedTranslation_equalityFreeDiagonal, fixedTranslation_equalityBoundDiagonal]
      · rw [substs1_equalityBoundLeft, fixedTranslation_equalityFree, fixedTranslation_equalityBoundLeft]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_equalityBoundRight, fixedTranslation_equalityFree, fixedTranslation_equalityBoundRight]
      · rw [substs1_positiveFvars _ _ _ _ relExt_relation_zero, fixedTranslation_equalityFree, fixedTranslation_equalityFree]
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_membershipBoundDiagonal, fixedTranslation_membershipFree, fixedTranslation_membershipBoundDiagonal]
      · rw [substs1_membershipBoundLeft, fixedTranslation_membershipFree, fixedTranslation_membershipBoundLeft]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_membershipBoundRight, fixedTranslation_membershipFree, fixedTranslation_membershipBoundRight]
      · rw [substs1_positiveFvars _ _ _ _ relExt_relation_one, fixedTranslation_membershipFree, fixedTranslation_membershipFree]

theorem fixedTranslation_negativeEqualityBoundDiagonal (bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = negValue (neighborhoodValue base base reserve) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,fixedTranslation_equalityBoundDiagonal]

theorem negativeAtom_substitution_translation (r a b j bound free base reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    F fixedFormulaTranslation ![substs1 SourceL (^&j) (^nrel (2 : M) r ?[a,b]),bound,free,base,reserve] =
      F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],pair (free.[j]) bound+1,free,(free.[j])+1,reserve] := by
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeEqualityBoundDiagonal, fixedTranslation_negativeEqualityFree, fixedTranslation_negativeEqualityBoundDiagonal]
      · rw [substs1_negativeEqualityBoundLeft, fixedTranslation_negativeEqualityFree, fixedTranslation_negativeEqualityBoundLeft]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeEqualityBoundRight, fixedTranslation_negativeEqualityFree, fixedTranslation_negativeEqualityBoundRight]
      · rw [substs1_negativeFvars _ _ _ _ relExt_relation_zero, fixedTranslation_negativeEqualityFree, fixedTranslation_negativeEqualityFree]
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeMembershipBoundDiagonal, fixedTranslation_negativeMembershipFree, fixedTranslation_negativeMembershipBoundDiagonal]
      · rw [substs1_negativeMembershipBoundLeft, fixedTranslation_negativeMembershipFree, fixedTranslation_negativeMembershipBoundLeft]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeMembershipBoundRight, fixedTranslation_negativeMembershipFree, fixedTranslation_negativeMembershipBoundRight]
      · rw [substs1_negativeFvars _ _ _ _ relExt_relation_one, fixedTranslation_negativeMembershipFree, fixedTranslation_negativeMembershipFree]

theorem positiveAtom_substitution_valid (r a b j : M)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    IsUFormula SourceL (substs1 SourceL (^&j) (^rel (2 : M) r ?[a,b])) := by
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_equalityBoundDiagonal]; simp [relExt_relation_zero]
      · rw [substs1_equalityBoundLeft]; simp [relExt_relation_zero]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_equalityBoundRight]; simp [relExt_relation_zero]
      · rw [substs1_positiveFvars _ _ _ _ relExt_relation_zero]; simp [relExt_relation_zero]
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_membershipBoundDiagonal]; simp [relExt_relation_one]
      · rw [substs1_membershipBoundLeft]; simp [relExt_relation_one]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_membershipBoundRight]; simp [relExt_relation_one]
      · rw [substs1_positiveFvars _ _ _ _ relExt_relation_one]; simp [relExt_relation_one]

theorem negativeAtom_substitution_valid (r a b j : M)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    IsUFormula SourceL (substs1 SourceL (^&j) (^nrel (2 : M) r ?[a,b])) := by
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeEqualityBoundDiagonal]; simp [relExt_relation_zero]
      · rw [substs1_negativeEqualityBoundLeft]; simp [relExt_relation_zero]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeEqualityBoundRight]; simp [relExt_relation_zero]
      · rw [substs1_negativeFvars _ _ _ _ relExt_relation_zero]; simp [relExt_relation_zero]
  · rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeMembershipBoundDiagonal]; simp [relExt_relation_one]
      · rw [substs1_negativeMembershipBoundLeft]; simp [relExt_relation_one]
    · rcases sourceSemitermOne_cases b hb with (rfl | ⟨k,rfl⟩)
      · rw [substs1_negativeMembershipBoundRight]; simp [relExt_relation_one]
      · rw [substs1_negativeFvars _ _ _ _ relExt_relation_one]; simp [relExt_relation_one]

/-- Internal substitution correctness for quantifier-free bodies, uniformly
for nonstandard formula codes. -/
theorem quantifierFree_substitution_translation (p j bound free base reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p) :
    IsUFormula SourceL (substs1 SourceL (^&j) p) ∧
    F fixedFormulaTranslation ![substs1 SourceL (^&j) p,bound,free,base,reserve] =
      F fixedFormulaTranslation ![p,pair (free.[j]) bound+1,free,(free.[j])+1,reserve] := by
  let e := pair bound (pair free (pair base reserve))
  let e' := pair (pair (free.[j]) bound+1) (pair free (pair ((free.[j])+1) reserve))
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  haveI : 𝚺₁-Function₁ (fun p : M => substs1 SourceL (^&j) p) := by
    unfold substs1
    definability
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q → IsSemiformula SourceL 1 q →
      IsUFormula SourceL (substs1 SourceL (^&j) q) ∧
      positiveTranslation e (substs1 SourceL (^&j) q) = positiveTranslation e' q) := by
    definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q → IsSemiformula SourceL 1 q →
      IsUFormula SourceL (substs1 SourceL (^&j) q) ∧
      positiveTranslation e (substs1 SourceL (^&j) q) = positiveTranslation e' q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv hqf hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      refine ⟨positiveAtom_substitution_valid r a b j hr ha hb,?_⟩
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact positiveAtom_substitution_translation r a b j bound free base reserve hr ha hb
    · intro arity r v hr hv hqf hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
      refine ⟨negativeAtom_substitution_valid r a b j hr ha hb,?_⟩
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact negativeAtom_substitution_translation r a b j bound free base reserve hr ha hb
    · intro _ _
      have hv : substs1 SourceL (^&j) (^⊤ : M) = ^⊤ := by unfold substs1; exact substs_verum _
      rw [hv]
      constructor
      · simp
      · dsimp only [e,e']
        rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro _ _
      have hv : substs1 SourceL (^&j) (^⊥ : M) = ^⊥ := by unfold substs1; exact substs_falsum _
      rw [hv]
      constructor
      · simp
      · dsimp only [e,e']
        rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
    · intro a b hau hbu iha ihb hqf hscope
      have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hscope
      have ia := iha (internalQuantifierFree_child _ _ _ hl hqf) hsa
      have ib := ihb (internalQuantifierFree_child _ _ _ hr hqf) hsb
      have hs : substs1 SourceL (^&j) (a ^⋏ b) =
          (substs1 SourceL (^&j) a) ^⋏ (substs1 SourceL (^&j) b) := by
        unfold substs1
        exact substs_and hau hbu
      rw [hs]
      constructor
      · exact IsUFormula.and.mpr ⟨ia.1,ib.1⟩
      · dsimp only [e,e'] at ia ib ⊢
        rw [positiveTranslation_model,positiveTranslation_model] at ia ib ⊢
        rw [fixedFormulaTranslation_and _ _ _ _ _ _ ia.1 ib.1,
          fixedFormulaTranslation_and _ _ _ _ _ _ hau hbu,ia.2,ib.2]
    · intro a b hau hbu iha ihb hqf hscope
      have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ia := iha (internalQuantifierFree_child _ _ _ hl hqf) hsa
      have ib := ihb (internalQuantifierFree_child _ _ _ hr hqf) hsb
      have hs : substs1 SourceL (^&j) (a ^⋎ b) =
          (substs1 SourceL (^&j) a) ^⋎ (substs1 SourceL (^&j) b) := by
        unfold substs1
        exact substs_or hau hbu
      rw [hs]
      constructor
      · exact IsUFormula.or.mpr ⟨ia.1,ib.1⟩
      · dsimp only [e,e'] at ia ib ⊢
        rw [positiveTranslation_model,positiveTranslation_model] at ia ib ⊢
        rw [fixedFormulaTranslation_or _ _ _ _ _ _ ia.1 ib.1,
          fixedFormulaTranslation_or _ _ _ _ _ _ hau hbu,ia.2,ib.2]
    · intro a hau ih hqf hscope
      exact False.elim (internalQuantifierFree_not_all a hqf)
    · intro a hau ih hqf hscope
      exact False.elim (internalQuantifierFree_not_ex a hqf)
  have h := hall p hp.isUFormula hqf hp
  dsimp only [e,e'] at h
  simpa only [positiveTranslation_model] using h

/-- Existential introduction for any internal quantifier-free body, using a
free-label witness below the fresh binder and reserve. -/
theorem targetExistsQF_freeWitness (p x c free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p)
    (hcx : c < x) (hfree : ∀ i : M, free.[i] < x) (hxz : x < reserve) :
    TargetProvable (impValue
      (F fixedFormulaTranslation ![p,pair c (0 : M)+1,free,c+1,reserve])
      (exValue x (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]))) := by
  let P := F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]
  let Q := F fixedFormulaTranslation ![p,pair c (0 : M)+1,free,c+1,reserve]
  let A := negValue P
  let B := negValue Q
  have hx0 : (0 : M) ≠ x := ne_of_lt (lt_of_le_of_lt zero_le hcx)
  have hcne : c ≠ x := ne_of_lt hcx
  have hzc : reserve ≠ c := ne_of_gt (lt_trans hcx hxz)
  have hzx : reserve ≠ x := ne_of_gt hxz
  have hrew0 := fullQF_binderRewrite p x c 0 free reserve hp hqf hzc hzx
  have hrew : TargetPremiseRewrite (eqValue c x) A B :=
    targetPremiseRewrite_neg _ _ _ hrew0
  let common := x+c+1
  have hxc : x < common := lt_of_le_of_lt (show x ≤ x+c from le_self_add) (lt_add_one _)
  have hbound : ∀ i ≤ p, (pair c (0 : M)+1).[i] ≠ x := by
    intro i _; exact singletonStack_avoids c x hcne hx0 i
  have hfx : ∀ i ≤ p, free.[i] ≠ x := by
    intro i _; exact ne_of_lt (hfree i)
  have hv := generalVacuity_below_all_codes x p (pair c (0 : M)+1) free common reserve
    hp.isUFormula hxc hbound hfx (ne_of_lt hxz)
  unfold GeneralVacuity at hv
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hv
  have hnorm := quantifierFree_anyBases p (pair c (0 : M)+1) free (c+1) common reserve hp.isUFormula hqf
  rw [←hnorm] at hv
  have hvB : TargetProvable (impValue B (allValue x B)) := negationVacuity x Q hv
  have hs : TargetProvable (impValue (allValue x A) B) :=
    specializeWithMirroredEquality_target x c A B hvB hrew.1
  let hq : Ctx [allValue x A,Q] Q := .assumption (by simp)
  let hall : Ctx [allValue x A,Q] (allValue x A) := .assumption (by simp)
  let hn : Ctx [allValue x A,Q] B := .mp hall (.closed hs)
  exact (Ctx.mp hq hn).deduction.deduction.empty

/-- Exact existential-rule field for an arbitrary quantifier-free source body,
at an actually seeded existential node. -/
theorem simRuleExs_quantifierFreeSeed (reserve e s p t d : M)
    (ha : SeedAdmission 0 reserve e (exsIntro s p t d))
    (hs : IsFormulaSet SourceL s) (hm : (^∃ p) ∈ s) (ht : IsTerm SourceL t)
    (hqf : InternalQuantifierFree p) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t p)) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ p)) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  have hbody : IsSemiformula SourceL 1 p := by
    have hf := hs _ hm
    simpa only [IsSemiformula.exs,zero_add] using hf
  have hrank : RankedAdmission e (exsIntro s p (^&j) d) := depthAdmission_ranked e _ ha.1
  have hb : simBound e = 0 := ha.2.2.1
  have hcx : (simFree e).[j] < simBase e := rankedEnvironment_free_lt e j hrank.1
  have hfree : ∀ i : M, (simFree e).[i] < simBase e := fun i => rankedEnvironment_free_lt e i hrank.1
  have hxz : simBase e < simReserve e :=
    partialAdmission_base_lt_reserve 0 e _ (rankedAdmission_to_partial 0 e _ hrank)
  apply simRuleExs_of_intro e s p (^&j) hs hm (by simp)
  rw [fixedFormulaTranslation_ex _ _ _ _ _ hbody.isUFormula]
  rw [(quantifierFree_substitution_translation p j (simBound e) (simFree e) (simBase e) (simReserve e) hbody hqf).2,hb]
  exact targetExistsQF_freeWitness p (simBase e) (simFree e).[j] (simFree e) (simReserve e)
    hbody hqf hcx hfree hxz

#print axioms targetExistsQF_freeWitness
#print axioms simRuleExs_quantifierFreeSeed
#print axioms quantifierFree_substitution_translation
#print axioms positiveAtom_substitution_valid
#print axioms negativeAtom_substitution_valid
#print axioms negativeAtom_substitution_translation
#print axioms positiveAtom_substitution_translation
end models
end PA194ModelLogic
