import PA194ModelOneLevelFresh
import PA194ModelQFConverse
import PA194ModelShallowFresh
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelFreshBoolean
import PA194ModelBelowFreshInduction
import PA194ModelQuantifierFreeFresh
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
local instance levelCharZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance levelCharOne : One M := ⟨F oneCode Fin.elim0⟩
local instance levelCharAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance levelCharMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance levelCharLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance levelCharIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]










/-- Every quantifier-free formula belongs to the one-level class. -/
theorem internalQuantifierFree_implies_oneLevel (p : M) (h : InternalQuantifierFree p) : OneLevelMembership p := by
  intro ⟨a,ha,_⟩
  exact h ⟨a,ha⟩

theorem oneLevelMembership_binary_intro (root a b : M)
    (hr0 : root ≠ 0) (hnotAll : ∀ c : M, root ≠ ^∀ c) (hnotEx : ∀ c : M, root ≠ ^∃ c)
    (hedges : ∀ child bit : M, SourceDirectEdge root child bit → child = a ∨ child = b)
    (ha : OneLevelMembership a) (hb : OneLevelMembership b) : OneLevelMembership root := by
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

theorem oneLevelMembership_and_iff (a b : M) :
    OneLevelMembership (a ^⋏ b) ↔ OneLevelMembership a ∧ OneLevelMembership b := by
  have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨oneLevelMembership_child _ _ _ hl h,oneLevelMembership_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply oneLevelMembership_binary_intro (a ^⋏ b) a b
    · change pair (4 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).1
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).2
    · intro child bit he; exact directEdge_and_child a b child bit he
    · exact ha
    · exact hb

theorem oneLevelMembership_or_iff (a b : M) :
    OneLevelMembership (a ^⋎ b) ↔ OneLevelMembership a ∧ OneLevelMembership b := by
  have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨oneLevelMembership_child _ _ _ hl h,oneLevelMembership_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply oneLevelMembership_binary_intro (a ^⋎ b) a b
    · change pair (5 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).1
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).2
    · intro child bit he; exact directEdge_or_child a b child bit he
    · exact ha
    · exact hb

theorem oneLevelMembership_all_iff (a : M) : OneLevelMembership (^∀ a) ↔ InternalMembershipQF a := by
  constructor
  · exact oneLevelMembership_all_body a
  · intro ha
    have hqf := ha.1
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

theorem oneLevelMembership_ex_iff (a : M) : OneLevelMembership (^∃ a) ↔ InternalMembershipQF a := by
  constructor
  · exact oneLevelMembership_ex_body a
  · intro ha
    have hqf := ha.1
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

/-- Positive membership atom codes meet the internally defined membership-only
quantifier-free condition. -/
theorem internalMembershipQF_positiveAtom (v : M) :
    InternalMembershipQF (^rel (2 : M) (1 : M) v) := by
  constructor
  · change InternalQuantifierFree (pair (0 : M) (pair 2 (pair 1 v))+1)
    exact internalQuantifierFree_leaf 0 (pair 2 (pair 1 v)) (Or.inl rfl)
  · intro ⟨w,h⟩
    rcases h with h | h
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 0 (pair (2 : M) (pair 1 v)) choices steps (Or.inl rfl)
      change F sourcePath ![steps, pair (0 : M) (pair 2 (pair 1 v))+1, choices] = _ at hpath
      rw [hstat] at hpath
      change pair (0 : M) (pair 2 (pair 1 v))+1 = pair (0 : M) (pair 2 (pair 0 w))+1 at hpath
      have h1 := (pair_ext_iff.mp (add_right_cancel hpath)).2
      have h2 := (pair_ext_iff.mp h1).2
      have h3 := (pair_ext_iff.mp h2).1
      norm_num at h3
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 0 (pair (2 : M) (pair 1 v)) choices steps (Or.inl rfl)
      change F sourcePath ![steps, pair (0 : M) (pair 2 (pair 1 v))+1, choices] = _ at hpath
      rw [hstat] at hpath
      have htag := congrArg (fun q : M => F nodeTag ![q]) hpath
      change F nodeTag ![pair (0 : M) (pair 2 (pair 1 v))+1] =
        F nodeTag ![pair (1 : M) (pair 2 (pair 0 w))+1] at htag
      rw [nodeTag_model,nodeTag_model] at htag
      norm_num at htag

theorem internalMembershipQF_negativeAtom (v : M) :
    InternalMembershipQF (^nrel (2 : M) (1 : M) v) := by
  constructor
  · change InternalQuantifierFree (pair (1 : M) (pair 2 (pair 1 v))+1)
    exact internalQuantifierFree_leaf 1 (pair 2 (pair 1 v)) (Or.inr (Or.inl rfl))
  · intro ⟨w,h⟩
    rcases h with h | h
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 1 (pair (2 : M) (pair 1 v)) choices steps (Or.inr (Or.inl rfl))
      change F sourcePath ![steps, pair (1 : M) (pair 2 (pair 1 v))+1, choices] = _ at hpath
      rw [hstat] at hpath
      have htag := congrArg (fun q : M => F nodeTag ![q]) hpath
      change F nodeTag ![pair (1 : M) (pair 2 (pair 1 v))+1] =
        F nodeTag ![pair (0 : M) (pair 2 (pair 0 w))+1] at htag
      rw [nodeTag_model,nodeTag_model] at htag
      norm_num at htag
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 1 (pair (2 : M) (pair 1 v)) choices steps (Or.inr (Or.inl rfl))
      change F sourcePath ![steps, pair (1 : M) (pair 2 (pair 1 v))+1, choices] = _ at hpath
      rw [hstat] at hpath
      change pair (1 : M) (pair 2 (pair 1 v))+1 = pair (1 : M) (pair 2 (pair 0 w))+1 at hpath
      have h1 := (pair_ext_iff.mp (add_right_cancel hpath)).2
      have h2 := (pair_ext_iff.mp h1).2
      have h3 := (pair_ext_iff.mp h2).1
      norm_num at h3

theorem binaryCode_not_equality (tag payload v : M) (ht : tag = 4 ∨ tag = 5) :
    pair tag payload+1 ≠ ^rel (2 : M) (0 : M) v ∧
      pair tag payload+1 ≠ ^nrel (2 : M) (0 : M) v := by
  constructor <;> intro h
  · have htag := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair tag payload+1] = F nodeTag ![pair (0 : M) (pair 2 (pair 0 v))+1] at htag
    rw [nodeTag_model,nodeTag_model] at htag
    rcases ht with rfl | rfl <;> norm_num at htag
  · have htag := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair tag payload+1] = F nodeTag ![pair (1 : M) (pair 2 (pair 0 v))+1] at htag
    rw [nodeTag_model,nodeTag_model] at htag
    rcases ht with rfl | rfl <;> norm_num at htag

theorem internalMembershipQF_binary_intro (root a b : M)
    (hr0 : root ≠ 0)
    (hnpos : ∀ v : M, root ≠ ^rel (2 : M) (0 : M) v)
    (hnneg : ∀ v : M, root ≠ ^nrel (2 : M) (0 : M) v)
    (hedges : ∀ child bit : M, SourceDirectEdge root child bit → child = a ∨ child = b)
    (hroot : InternalQuantifierFree root)
    (ha : InternalMembershipQF a) (hb : InternalMembershipQF b) : InternalMembershipQF root := by
  refine ⟨hroot,?_⟩
  intro ⟨v,h⟩
  rcases h with h | h
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^rel (2 : M) (0 : M) v) hr0 (hnpos v) h
    rcases hedges child bit he with rfl | rfl
    · exact ha.2 ⟨v,Or.inl hd⟩
    · exact hb.2 ⟨v,Or.inl hd⟩
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^nrel (2 : M) (0 : M) v) hr0 (hnneg v) h
    rcases hedges child bit he with rfl | rfl
    · exact ha.2 ⟨v,Or.inr hd⟩
    · exact hb.2 ⟨v,Or.inr hd⟩

theorem internalMembershipQF_and_iff (a b : M) :
    InternalMembershipQF (a ^⋏ b) ↔ InternalMembershipQF a ∧ InternalMembershipQF b := by
  have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨internalMembershipQF_child _ _ _ hl h,internalMembershipQF_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply internalMembershipQF_binary_intro (a ^⋏ b) a b
    · change pair (4 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro v; exact (binaryCode_not_equality 4 (pair a b) v (Or.inl rfl)).1
    · intro v; exact (binaryCode_not_equality 4 (pair a b) v (Or.inl rfl)).2
    · intro child bit he; exact directEdge_and_child a b child bit he
    · exact (internalQuantifierFree_and_iff a b).2 ⟨ha.1,hb.1⟩
    · exact ha
    · exact hb

theorem internalMembershipQF_or_iff (a b : M) :
    InternalMembershipQF (a ^⋎ b) ↔ InternalMembershipQF a ∧ InternalMembershipQF b := by
  have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨internalMembershipQF_child _ _ _ hl h,internalMembershipQF_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply internalMembershipQF_binary_intro (a ^⋎ b) a b
    · change pair (5 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro v; exact (binaryCode_not_equality 5 (pair a b) v (Or.inr rfl)).1
    · intro v; exact (binaryCode_not_equality 5 (pair a b) v (Or.inr rfl)).2
    · intro child bit he; exact directEdge_or_child a b child bit he
    · exact (internalQuantifierFree_or_iff a b).2 ⟨ha.1,hb.1⟩
    · exact ha
    · exact hb

#print axioms internalQuantifierFree_implies_oneLevel
#print axioms oneLevelMembership_and_iff
#print axioms oneLevelMembership_or_iff
#print axioms oneLevelMembership_all_iff
#print axioms oneLevelMembership_ex_iff
#print axioms internalMembershipQF_positiveAtom
#print axioms internalMembershipQF_negativeAtom
#print axioms internalMembershipQF_and_iff
#print axioms internalMembershipQF_or_iff
end models
end PA194ModelLogic
