import PA194ModelOneLevelReflexive
import PA194ModelOneLevelCharacterization
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
local instance reflexiveExampleZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance reflexiveExampleOne : One M := ⟨F oneCode Fin.elim0⟩
local instance reflexiveExampleAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance reflexiveExampleMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance reflexiveExampleLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance reflexiveExampleIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]










theorem doubleton_refl_arguments (a : M) : (?[a,a] : M).[0] = (?[a,a] : M).[1] := by
  have h1 : (1 : M) = (0 : M)+1 := by simp
  rw [h1,nth_adjoin_zero,nth_adjoin_succ,nth_adjoin_zero]

theorem internalReflexiveQF_positiveDiagonal (a : M) :
    InternalReflexiveQF (^rel (2 : M) (0 : M) ?[a,a]) := by
  constructor
  · change InternalQuantifierFree (pair (0 : M) (pair 2 (pair 0 (?[a,a] : M)))+1)
    exact internalQuantifierFree_leaf 0 (pair 2 (pair 0 (?[a,a] : M))) (Or.inl rfl)
  · intro ⟨v,hn,h⟩
    rcases h with h | h
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 0 (pair (2 : M) (pair 0 (?[a,a] : M))) choices steps (Or.inl rfl)
      change F sourcePath ![steps, pair (0 : M) (pair 2 (pair 0 (?[a,a] : M)))+1, choices] = _ at hpath
      rw [hstat] at hpath
      change pair (0 : M) (pair 2 (pair 0 (?[a,a] : M)))+1 = pair (0 : M) (pair 2 (pair 0 v))+1 at hpath
      have h1 := (pair_ext_iff.mp (add_right_cancel hpath)).2
      have h2 := (pair_ext_iff.mp h1).2
      have h3 := (pair_ext_iff.mp h2).2
      subst v
      exact hn (doubleton_refl_arguments a)
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 0 (pair (2 : M) (pair 0 (?[a,a] : M))) choices steps (Or.inl rfl)
      change F sourcePath ![steps, pair (0 : M) (pair 2 (pair 0 (?[a,a] : M)))+1, choices] = _ at hpath
      rw [hstat] at hpath
      have htag := congrArg (fun q : M => F nodeTag ![q]) hpath
      change F nodeTag ![pair (0 : M) (pair 2 (pair 0 (?[a,a] : M)))+1] =
        F nodeTag ![pair (1 : M) (pair 2 (pair 0 v))+1] at htag
      rw [nodeTag_model,nodeTag_model] at htag
      norm_num at htag

theorem internalReflexiveQF_negativeDiagonal (a : M) :
    InternalReflexiveQF (^nrel (2 : M) (0 : M) ?[a,a]) := by
  constructor
  · change InternalQuantifierFree (pair (1 : M) (pair 2 (pair 0 (?[a,a] : M)))+1)
    exact internalQuantifierFree_leaf 1 (pair 2 (pair 0 (?[a,a] : M))) (Or.inr (Or.inl rfl))
  · intro ⟨v,hn,h⟩
    rcases h with h | h
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 1 (pair (2 : M) (pair 0 (?[a,a] : M))) choices steps (Or.inr (Or.inl rfl))
      change F sourcePath ![steps, pair (1 : M) (pair 2 (pair 0 (?[a,a] : M)))+1, choices] = _ at hpath
      rw [hstat] at hpath
      have htag := congrArg (fun q : M => F nodeTag ![q]) hpath
      change F nodeTag ![pair (1 : M) (pair 2 (pair 0 (?[a,a] : M)))+1] =
        F nodeTag ![pair (0 : M) (pair 2 (pair 0 v))+1] at htag
      rw [nodeTag_model,nodeTag_model] at htag
      norm_num at htag
    · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ h
      have hstat := sourcePath_leaf_stationary 1 (pair (2 : M) (pair 0 (?[a,a] : M))) choices steps (Or.inr (Or.inl rfl))
      change F sourcePath ![steps, pair (1 : M) (pair 2 (pair 0 (?[a,a] : M)))+1, choices] = _ at hpath
      rw [hstat] at hpath
      change pair (1 : M) (pair 2 (pair 0 (?[a,a] : M)))+1 = pair (1 : M) (pair 2 (pair 0 v))+1 at hpath
      have h1 := (pair_ext_iff.mp (add_right_cancel hpath)).2
      have h2 := (pair_ext_iff.mp h1).2
      have h3 := (pair_ext_iff.mp h2).2
      subst v
      exact hn (doubleton_refl_arguments a)

theorem internalReflexiveQF_binary_intro (root a b : M)
    (hr0 : root ≠ 0)
    (hnpos : ∀ v : M, root ≠ ^rel (2 : M) (0 : M) v)
    (hnneg : ∀ v : M, root ≠ ^nrel (2 : M) (0 : M) v)
    (hedges : ∀ child bit : M, SourceDirectEdge root child bit → child = a ∨ child = b)
    (hroot : InternalQuantifierFree root)
    (ha : InternalReflexiveQF a) (hb : InternalReflexiveQF b) : InternalReflexiveQF root := by
  refine ⟨hroot,?_⟩
  intro ⟨v,hn,h⟩
  rcases h with h | h
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^rel (2 : M) (0 : M) v) hr0 (hnpos v) h
    rcases hedges child bit he with rfl | rfl
    · exact ha.2 ⟨v,hn,Or.inl hd⟩
    · exact hb.2 ⟨v,hn,Or.inl hd⟩
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^nrel (2 : M) (0 : M) v) hr0 (hnneg v) h
    rcases hedges child bit he with rfl | rfl
    · exact ha.2 ⟨v,hn,Or.inr hd⟩
    · exact hb.2 ⟨v,hn,Or.inr hd⟩

theorem internalReflexiveQF_and_iff (a b : M) :
    InternalReflexiveQF (a ^⋏ b) ↔ InternalReflexiveQF a ∧ InternalReflexiveQF b := by
  have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨internalReflexiveQF_child _ _ _ hl h,internalReflexiveQF_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply internalReflexiveQF_binary_intro (a ^⋏ b) a b
    · change pair (4 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro v; exact (binaryCode_not_equality 4 (pair a b) v (Or.inl rfl)).1
    · intro v; exact (binaryCode_not_equality 4 (pair a b) v (Or.inl rfl)).2
    · intro child bit he; exact directEdge_and_child a b child bit he
    · exact (internalQuantifierFree_and_iff a b).2 ⟨ha.1,hb.1⟩
    · exact ha
    · exact hb

theorem internalReflexiveQF_or_iff (a b : M) :
    InternalReflexiveQF (a ^⋎ b) ↔ InternalReflexiveQF a ∧ InternalReflexiveQF b := by
  have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨internalReflexiveQF_child _ _ _ hl h,internalReflexiveQF_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply internalReflexiveQF_binary_intro (a ^⋎ b) a b
    · change pair (5 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro v; exact (binaryCode_not_equality 5 (pair a b) v (Or.inr rfl)).1
    · intro v; exact (binaryCode_not_equality 5 (pair a b) v (Or.inr rfl)).2
    · intro child bit he; exact directEdge_or_child a b child bit he
    · exact (internalQuantifierFree_or_iff a b).2 ⟨ha.1,hb.1⟩
    · exact ha
    · exact hb


theorem internalQuantifierFree_implies_oneLevelReflexive (p : M) (h : InternalQuantifierFree p) : OneLevelReflexive p := by
  intro ⟨a,ha,_⟩
  exact h ⟨a,ha⟩

theorem oneLevelReflexive_binary_intro (root a b : M)
    (hr0 : root ≠ 0) (hnotAll : ∀ c : M, root ≠ ^∀ c) (hnotEx : ∀ c : M, root ≠ ^∃ c)
    (hedges : ∀ child bit : M, SourceDirectEdge root child bit → child = a ∨ child = b)
    (ha : OneLevelReflexive a) (hb : OneLevelReflexive b) : OneLevelReflexive root := by
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

theorem oneLevelReflexive_and_iff (a b : M) :
    OneLevelReflexive (a ^⋏ b) ↔ OneLevelReflexive a ∧ OneLevelReflexive b := by
  have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨oneLevelReflexive_child _ _ _ hl h,oneLevelReflexive_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply oneLevelReflexive_binary_intro (a ^⋏ b) a b
    · change pair (4 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).1
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).2
    · intro child bit he; exact directEdge_and_child a b child bit he
    · exact ha
    · exact hb

theorem oneLevelReflexive_or_iff (a b : M) :
    OneLevelReflexive (a ^⋎ b) ↔ OneLevelReflexive a ∧ OneLevelReflexive b := by
  have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨oneLevelReflexive_child _ _ _ hl h,oneLevelReflexive_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply oneLevelReflexive_binary_intro (a ^⋎ b) a b
    · change pair (5 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).1
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).2
    · intro child bit he; exact directEdge_or_child a b child bit he
    · exact ha
    · exact hb

theorem oneLevelReflexive_all_iff (a : M) : OneLevelReflexive (^∀ a) ↔ InternalReflexiveQF a := by
  constructor
  · exact oneLevelReflexive_all_body a
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

theorem oneLevelReflexive_ex_iff (a : M) : OneLevelReflexive (^∃ a) ↔ InternalReflexiveQF a := by
  constructor
  · exact oneLevelReflexive_ex_body a
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


theorem reflexiveEquality_strictExample (a : M) :
    OneLevelReflexive (^∀ (^rel (2 : M) (0 : M) ?[a,a])) ∧
      ¬ OneLevelMembership (^∀ (^rel (2 : M) (0 : M) ?[a,a])) := by
  constructor
  · exact (oneLevelReflexive_all_iff _).2 (internalReflexiveQF_positiveDiagonal a)
  · intro h
    have hmem := oneLevelMembership_all_body _ h
    apply hmem.2
    exact ⟨?[a,a],Or.inl (codedSyntacticDescendant_self (^rel (2 : M) (0 : M) ?[a,a]))⟩

#print axioms reflexiveEquality_strictExample
#print axioms oneLevelReflexive_and_iff
#print axioms oneLevelReflexive_or_iff
#print axioms oneLevelReflexive_all_iff
#print axioms oneLevelReflexive_ex_iff
#print axioms internalReflexiveQF_and_iff
#print axioms internalReflexiveQF_or_iff
#print axioms internalReflexiveQF_positiveDiagonal
#print axioms internalReflexiveQF_negativeDiagonal
end models
end PA194ModelLogic
