import PA194ModelAtomicAlpha
import PA194ModelSeedEnvironment
import PA194ModelQFConverse
import PA194ModelDescendantComplexity
import PA194ModelFreshBoolean
import PA194ModelBelowFreshInduction
import PA194ModelQuantifierFreeFresh
import PA194ModelSeedEnvironment
import PA194ModelQFConverse
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
local instance shallowZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance shallowOne : One M := ⟨F oneCode Fin.elim0⟩
local instance shallowAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance shallowMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance shallowLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance shallowIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]








/-- A raw source code is a positive or negative membership atom. -/
def PlainMembershipAtom (a : M) : Prop :=
  ∃ v ≤ a, a = ^rel (2 : M) (1 : M) v ∨ a = ^nrel (2 : M) (1 : M) v

theorem plainMembershipAtom_pi (M_dummy : M) : 𝚷₁-Predicate (PlainMembershipAtom : M → Prop) := by
  unfold PlainMembershipAtom
  definability

theorem plainMembershipAtom_sigma : 𝚺₁-Predicate (PlainMembershipAtom : M → Prop) := by
  unfold PlainMembershipAtom
  definability

/-- Every internally reached binder has a membership-atom body. -/
def ShallowMembership (p : M) : Prop :=
  ¬ ∃ a : M, (CodedSyntacticDescendant p (^∀ a) ∨ CodedSyntacticDescendant p (^∃ a)) ∧
    ¬ PlainMembershipAtom a

theorem shallowMembership_definable : 𝚷₁-Predicate (ShallowMembership : M → Prop) := by
  haveI : 𝚺₁-Relation (CodedSyntacticDescendant (M := M)) := codedSyntacticDescendant_definable
  haveI : 𝚷₁-Predicate (PlainMembershipAtom : M → Prop) := plainMembershipAtom_pi 0
  unfold ShallowMembership
  definability

theorem shallowMembership_child (parent child bit : M)
    (he : SourceDirectEdge parent child bit) (h : ShallowMembership parent) : ShallowMembership child := by
  intro ⟨a,ha,hbad⟩
  apply h
  refine ⟨a,?_,hbad⟩
  rcases ha with ha | ha
  · exact Or.inl (codedSyntacticDescendant_extend parent child (^∀ a) bit he ha)
  · exact Or.inr (codedSyntacticDescendant_extend parent child (^∃ a) bit he ha)

theorem shallowMembership_all_body (a : M) (h : ShallowMembership (^∀ a)) : PlainMembershipAtom a := by
  by_contra hn
  exact h ⟨a,Or.inl (codedSyntacticDescendant_self _),hn⟩

theorem shallowMembership_ex_body (a : M) (h : ShallowMembership (^∃ a)) : PlainMembershipAtom a := by
  by_contra hn
  exact h ⟨a,Or.inr (codedSyntacticDescendant_self _),hn⟩

theorem singletonFormulaSet (q : M) (hq : IsFormula SourceL q) : IsFormulaSet SourceL ({q} : M) := by
  intro a ha
  have ha' : a = q := mem_singleton_iff.mp ha
  simpa only [ha'] using hq

theorem freshBridge_definable (e : M) : 𝚺₁-Predicate (FreshBridge (M := M) e) := by
  haveI : 𝚺₁-Function₂ (negatedTranslation : M → M → M) :=
    (numericalTranslation (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₂ (impValue : M → M → M) := (numericalCalc (M := M)).imp_defined.to_definable
  haveI : 𝚺₁-Predicate (TargetProvable : M → Prop) := targetProvable_definable
  unfold FreshBridge
  definability

theorem shallowFresh_all_codes (e p d : M) (hp : IsFormula SourceL p)
    (hsh : ShallowMembership p) (ha : RankedAdmission e d) (hb : simBound e = 0) : FreshBridge e p := by
  haveI : 𝚷₁-Predicate (ShallowMembership : M → Prop) := shallowMembership_definable
  haveI : 𝚺₁-Predicate (FreshBridge (M := M) e) := freshBridge_definable e
  have hdef : 𝚺₁-Predicate (fun q : M => ShallowMembership q → IsFormula SourceL q → FreshBridge e q) := by
    definability
  have hall : ∀ q, IsUFormula SourceL q → ShallowMembership q → IsFormula SourceL q → FreshBridge e q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv hsh hform
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
      have hbody := IsSemiformula.rel.mp hform
      obtain ⟨hca,hcb⟩ := IsSemitermVec.doubleton.mp hbody.2
      obtain ⟨i,rfl⟩ := sourceClosedTerm_is_fvar a hca
      obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar b hcb
      have hxi := ne_of_gt (rankedEnvironment_free_lt e i ha.1)
      have hxj := ne_of_gt (rankedEnvironment_free_lt e j ha.1)
      have hxz := ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))
      have hres := simRuleAllFresh_positiveAtom e r (^&i) (^&j) hr (by simp) (by simp)
        (by simpa only [termLabel_free_nth] using hxi)
        (by simpa only [termLabel_free_nth] using hxj) hxz
      exact hres
    · intro arity r v hr hv hsh hform
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
      have hbody := IsSemiformula.nrel.mp hform
      obtain ⟨hca,hcb⟩ := IsSemitermVec.doubleton.mp hbody.2
      obtain ⟨i,rfl⟩ := sourceClosedTerm_is_fvar a hca
      obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar b hcb
      have hxi := ne_of_gt (rankedEnvironment_free_lt e i ha.1)
      have hxj := ne_of_gt (rankedEnvironment_free_lt e j ha.1)
      have hxz := ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))
      have hres := simRuleAllFresh_negativeAtom e r (^&i) (^&j) hr (by simp) (by simp)
        (by simpa only [termLabel_free_nth] using hxi)
        (by simpa only [termLabel_free_nth] using hxj) hxz
      exact hres
    · intro hsh hform
      exact freshBridge_verum e
    · intro hsh hform
      exact freshBridge_falsum e
    · intro a b hau hbu iha ihb hsh hform
      have hleft : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hfa,hfb⟩ := IsSemiformula.and.mp hform
      exact freshBridge_and e a b hau hbu
        (iha (shallowMembership_child _ _ _ hleft hsh) hfa)
        (ihb (shallowMembership_child _ _ _ hright hsh) hfb)
    · intro a b hau hbu iha ihb hsh hform
      have hleft : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hfa,hfb⟩ := IsSemiformula.or.mp hform
      exact freshBridge_or e a b hau hbu
        (iha (shallowMembership_child _ _ _ hleft hsh) hfa)
        (ihb (shallowMembership_child _ _ _ hright hsh) hfb)
    · intro a hau ih hsh hform
      obtain ⟨v,_,hv | hv⟩ := shallowMembership_all_body a hsh
      · subst a
        have hs : IsFormulaSet SourceL ({^∀ (^rel (2 : M) (1 : M) v)} : M) := singletonFormulaSet _ hform
        have hm : (^∀ (^rel (2 : M) (1 : M) v)) ∈ ({^∀ (^rel (2 : M) (1 : M) v)} : M) := mem_singleton_iff.mpr rfl
        exact simRuleAllFresh_allMembershipCode e _ v d hs hm ha hb
      · subst a
        have hs : IsFormulaSet SourceL ({^∀ (^nrel (2 : M) (1 : M) v)} : M) := singletonFormulaSet _ hform
        have hm : (^∀ (^nrel (2 : M) (1 : M) v)) ∈ ({^∀ (^nrel (2 : M) (1 : M) v)} : M) := mem_singleton_iff.mpr rfl
        exact simRuleAllFresh_allNegativeMembershipCode e _ v d hs hm ha hb
    · intro a hau ih hsh hform
      obtain ⟨v,_,hv | hv⟩ := shallowMembership_ex_body a hsh
      · subst a
        have hs : IsFormulaSet SourceL ({^∃ (^rel (2 : M) (1 : M) v)} : M) := singletonFormulaSet _ hform
        have hm : (^∃ (^rel (2 : M) (1 : M) v)) ∈ ({^∃ (^rel (2 : M) (1 : M) v)} : M) := mem_singleton_iff.mpr rfl
        exact simRuleAllFresh_exMembershipCode e _ v d hs hm ha hb
      · subst a
        have hs : IsFormulaSet SourceL ({^∃ (^nrel (2 : M) (1 : M) v)} : M) := singletonFormulaSet _ hform
        have hm : (^∃ (^nrel (2 : M) (1 : M) v)) ∈ ({^∃ (^nrel (2 : M) (1 : M) v)} : M) := mem_singleton_iff.mpr rfl
        exact simRuleAllFresh_exNegativeMembershipCode e _ v d hs hm ha hb
  exact hall p hp.isUFormula hsh hp

/-- The exact seeded `ruleAllFresh` field for any shallow-membership formula
in the source sequent. -/
theorem simRuleAllFresh_shallowSeed (reserve e s p q d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s p d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s) (hq : q ∈ s)
    (hsh : ShallowMembership q) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalQuant.all (simBase e) (numericalTranslation.tr e q))) :=
  shallowFresh_all_codes e q _ (hs _ hq) hsh (depthAdmission_ranked e _ ha.1) ha.2.2.1

theorem internalQuantifierFree_implies_shallow (p : M) (h : InternalQuantifierFree p) : ShallowMembership p := by
  intro ⟨a,ha,_⟩
  exact h ⟨a,ha⟩

theorem plainMembershipAtom_quantifierFree (a : M) (h : PlainMembershipAtom a) : InternalQuantifierFree a := by
  obtain ⟨v,_,h | h⟩ := h
  · subst a
    change InternalQuantifierFree (pair (0 : M) (pair 2 (pair 1 v))+1)
    exact internalQuantifierFree_leaf 0 (pair 2 (pair 1 v)) (Or.inl rfl)
  · subst a
    change InternalQuantifierFree (pair (1 : M) (pair 2 (pair 1 v))+1)
    exact internalQuantifierFree_leaf 1 (pair 2 (pair 1 v)) (Or.inr (Or.inl rfl))

theorem shallowMembership_binary_intro (root a b : M)
    (hr0 : root ≠ 0) (hnotAll : ∀ c : M, root ≠ ^∀ c) (hnotEx : ∀ c : M, root ≠ ^∃ c)
    (hedges : ∀ child bit : M, SourceDirectEdge root child bit → child = a ∨ child = b)
    (ha : ShallowMembership a) (hb : ShallowMembership b) : ShallowMembership root := by
  intro ⟨c,h,hbad⟩
  rcases h with h | h
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^∀ c) hr0 (hnotAll c) h
    rcases hedges child bit he with rfl | rfl
    · exact ha ⟨c,Or.inl hd,hbad⟩
    · exact hb ⟨c,Or.inl hd,hbad⟩
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^∃ c) hr0 (hnotEx c) h
    rcases hedges child bit he with rfl | rfl
    · exact ha ⟨c,Or.inr hd,hbad⟩
    · exact hb ⟨c,Or.inr hd,hbad⟩

theorem shallowMembership_and_iff (a b : M) :
    ShallowMembership (a ^⋏ b) ↔ ShallowMembership a ∧ ShallowMembership b := by
  have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨shallowMembership_child _ _ _ hl h,shallowMembership_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply shallowMembership_binary_intro (a ^⋏ b) a b
    · change pair (4 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).1
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).2
    · intro child bit he; exact directEdge_and_child a b child bit he
    · exact ha
    · exact hb

theorem shallowMembership_or_iff (a b : M) :
    ShallowMembership (a ^⋎ b) ↔ ShallowMembership a ∧ ShallowMembership b := by
  have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨shallowMembership_child _ _ _ hl h,shallowMembership_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply shallowMembership_binary_intro (a ^⋎ b) a b
    · change pair (5 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).1
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).2
    · intro child bit he; exact directEdge_or_child a b child bit he
    · exact ha
    · exact hb


theorem directEdge_all_child (a child bit : M) (he : SourceDirectEdge (^∀ a) child bit) : child = a := by
  rcases he with ⟨u,v,h,hc,_⟩ | ⟨u,v,h,hc,_⟩ | ⟨u,h,hc,_⟩ | ⟨u,h,hc,_⟩
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (6 : M) a+1] = F nodeTag ![pair (4 : M) (pair u v)+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (6 : M) a+1] = F nodeTag ![pair (5 : M) (pair u v)+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · change pair (6 : M) a+1 = pair (6 : M) u+1 at h
    have hu := (pair_ext_iff.mp (add_right_cancel h)).2
    exact hc.trans hu.symm
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (6 : M) a+1] = F nodeTag ![pair (7 : M) u+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht

theorem directEdge_ex_child (a child bit : M) (he : SourceDirectEdge (^∃ a) child bit) : child = a := by
  rcases he with ⟨u,v,h,hc,_⟩ | ⟨u,v,h,hc,_⟩ | ⟨u,h,hc,_⟩ | ⟨u,h,hc,_⟩
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (7 : M) a+1] = F nodeTag ![pair (4 : M) (pair u v)+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (7 : M) a+1] = F nodeTag ![pair (5 : M) (pair u v)+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (7 : M) a+1] = F nodeTag ![pair (6 : M) u+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · change pair (7 : M) a+1 = pair (7 : M) u+1 at h
    have hu := (pair_ext_iff.mp (add_right_cancel h)).2
    exact hc.trans hu.symm

theorem allCode_ne_exCode (a b : M) : (^∀ a) ≠ (^∃ b) := by
  intro h
  have ht := congrArg (fun p : M => F nodeTag ![p]) h
  change F nodeTag ![pair (6 : M) a+1] = F nodeTag ![pair (7 : M) b+1] at ht
  rw [nodeTag_model,nodeTag_model] at ht
  norm_num at ht

theorem shallowMembership_all_iff (a : M) : ShallowMembership (^∀ a) ↔ PlainMembershipAtom a := by
  constructor
  · exact shallowMembership_all_body a
  · intro ha
    have hqf := plainMembershipAtom_quantifierFree a ha
    have hn0 : (^∀ a) ≠ 0 := by
      change pair (6 : M) a+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    intro ⟨b,h,hbad⟩
    rcases h with h | h
    · by_cases heq : (^∀ a) = (^∀ b)
      · change pair (6 : M) a+1 = pair (6 : M) b+1 at heq
        have hab := (pair_ext_iff.mp (add_right_cancel heq)).2
        subst b
        exact hbad ha
      · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge (^∀ a) (^∀ b) hn0 heq h
        have hc := directEdge_all_child a child bit he
        subst child
        exact hqf ⟨b,Or.inl hd⟩
    · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge (^∀ a) (^∃ b) hn0 (allCode_ne_exCode a b) h
      have hc := directEdge_all_child a child bit he
      subst child
      exact hqf ⟨b,Or.inr hd⟩

theorem shallowMembership_ex_iff (a : M) : ShallowMembership (^∃ a) ↔ PlainMembershipAtom a := by
  constructor
  · exact shallowMembership_ex_body a
  · intro ha
    have hqf := plainMembershipAtom_quantifierFree a ha
    have hn0 : (^∃ a) ≠ 0 := by
      change pair (7 : M) a+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    intro ⟨b,h,hbad⟩
    rcases h with h | h
    · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge (^∃ a) (^∀ b) hn0 (Ne.symm (allCode_ne_exCode b a)) h
      have hc := directEdge_ex_child a child bit he
      subst child
      exact hqf ⟨b,Or.inl hd⟩
    · by_cases heq : (^∃ a) = (^∃ b)
      · change pair (7 : M) a+1 = pair (7 : M) b+1 at heq
        have hab := (pair_ext_iff.mp (add_right_cancel heq)).2
        subst b
        exact hbad ha
      · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge (^∃ a) (^∃ b) hn0 heq h
        have hc := directEdge_ex_child a child bit he
        subst child
        exact hqf ⟨b,Or.inr hd⟩

#print axioms plainMembershipAtom_pi
#print axioms plainMembershipAtom_sigma
#print axioms shallowMembership_definable
#print axioms shallowMembership_child
#print axioms shallowMembership_all_body
#print axioms shallowMembership_ex_body
#print axioms singletonFormulaSet
#print axioms freshBridge_definable
#print axioms shallowFresh_all_codes
#print axioms simRuleAllFresh_shallowSeed
#print axioms internalQuantifierFree_implies_shallow
#print axioms plainMembershipAtom_quantifierFree
#print axioms shallowMembership_and_iff
#print axioms shallowMembership_or_iff
#print axioms directEdge_all_child
#print axioms directEdge_ex_child
#print axioms shallowMembership_all_iff
#print axioms shallowMembership_ex_iff
end models
end PA194ModelLogic
