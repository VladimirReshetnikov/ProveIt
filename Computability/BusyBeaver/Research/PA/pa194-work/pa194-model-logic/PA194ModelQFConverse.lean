import PA194ModelQuantifierFreeFresh
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
local instance qfConverseZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfConverseOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfConverseAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfConverseMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfConverseLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfConverseIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- A nontrivial coded syntactic chain starting at a nonzero code has a
first constructor edge followed by a coded chain. -/
theorem codedDescendant_firstEdge (root target : M) (hr0 : root ≠ 0) (hrt : root ≠ target)
    (h : CodedSyntacticDescendant root target) :
    ∃ child bit : M, SourceDirectEdge root child bit ∧ CodedSyntacticDescendant child target := by
  obtain ⟨nodes,length,hchain,hroot,htarget⟩ := h
  rcases zero_or_succ length with hz | ⟨n,hn⟩
  · rw [hz] at htarget
    exact False.elim (hrt (hroot.symm.trans htarget))
  · have hnodes : nodes ≠ 0 := by
      intro hz
      rw [hz] at hroot
      have hzero : F PA194TargetStep.lookup ![(0 : M),(0 : M)] = 0 := by
        rw [←termLabel_free (0 : M) (0 : M) (0 : M),termLabel_free_nth]
        simp
      rw [hzero] at hroot
      exact hr0 hroot.symm
    rcases nil_or_adjoin nodes with hz | ⟨head,tail,hnode⟩
    · exact False.elim (hnodes hz)
    rw [adjoin_def] at hnode
    have hfirst : F PA194TargetStep.lookup ![(0 : M),nodes] = head := by
      rw [hnode]
      exact modelLookupZero firstProjection secondProjection firstProjection_certified head tail
    have hhead : head = root := hfirst.symm.trans hroot
    have hshift (j : M) : F PA194TargetStep.lookup ![j+1,nodes] = F PA194TargetStep.lookup ![j,tail] := by
      rw [hnode]
      exact modelLookupConsSucc firstProjection secondProjection secondProjection_certified j head tail
    have hnpos : (0 : M) < length := by rw [hn]; exact lt_of_le_of_lt zero_le (lt_add_one n)
    obtain ⟨bit,he⟩ := hchain 0 hnpos
    rw [hfirst] at he
    have hs0 : F PA194TargetStep.lookup ![(1 : M),nodes] = F PA194TargetStep.lookup ![0,tail] := by
      simpa only [zero_add] using hshift 0
    simp only [zero_add] at he
    rw [hhead,hs0] at he
    have he' : SourceDirectEdge root (F PA194TargetStep.lookup ![0,tail]) bit := he
    refine ⟨_,bit,he',tail,n,?_,rfl,?_⟩
    · intro j hj
      have hj' : j+1 < length := by
        rw [hn]
        simpa only [add_comm] using add_lt_add_right hj 1
      obtain ⟨k,hk⟩ := hchain (j+1) hj'
      refine ⟨k,?_⟩
      rw [hshift j,hshift (j+1)] at hk
      exact hk
    · rw [hn,hshift n] at htarget
      exact htarget

/-- Direct edges from a conjunction select exactly one displayed child. -/
theorem directEdge_and_child (a b child bit : M) (he : SourceDirectEdge (a ^⋏ b) child bit) :
    child = a ∨ child = b := by
  rcases he with ⟨u,v,h,hc,_⟩ | ⟨u,v,h,hc,_⟩ | ⟨u,h,_,_⟩ | ⟨u,h,_,_⟩
  · change pair (4 : M) (pair a b)+1 = pair (4 : M) (pair u v)+1 at h
    have hp := (pair_ext_iff.mp (add_right_cancel h)).2
    obtain ⟨hu,hv⟩ := pair_ext_iff.mp hp
    simpa only [←hu,←hv] using hc
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (4 : M) (pair a b)+1] = F nodeTag ![pair (5 : M) (pair u v)+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (4 : M) (pair a b)+1] = F nodeTag ![pair (6 : M) u+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (4 : M) (pair a b)+1] = F nodeTag ![pair (7 : M) u+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht

theorem directEdge_or_child (a b child bit : M) (he : SourceDirectEdge (a ^⋎ b) child bit) :
    child = a ∨ child = b := by
  rcases he with ⟨u,v,h,hc,_⟩ | ⟨u,v,h,hc,_⟩ | ⟨u,h,_,_⟩ | ⟨u,h,_,_⟩
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (5 : M) (pair a b)+1] = F nodeTag ![pair (4 : M) (pair u v)+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · change pair (5 : M) (pair a b)+1 = pair (5 : M) (pair u v)+1 at h
    have hp := (pair_ext_iff.mp (add_right_cancel h)).2
    obtain ⟨hu,hv⟩ := pair_ext_iff.mp hp
    simpa only [←hu,←hv] using hc
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (5 : M) (pair a b)+1] = F nodeTag ![pair (6 : M) u+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht
  · have ht := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair (5 : M) (pair a b)+1] = F nodeTag ![pair (7 : M) u+1] at ht
    rw [nodeTag_model,nodeTag_model] at ht
    norm_num at ht

theorem binaryCode_not_binders (tag payload a : M) (ht : tag = 4 ∨ tag = 5) :
    pair tag payload+1 ≠ (^∀ a) ∧ pair tag payload+1 ≠ (^∃ a) := by
  constructor <;> intro h
  · have htag := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair tag payload+1] = F nodeTag ![pair (6 : M) a+1] at htag
    rw [nodeTag_model,nodeTag_model] at htag
    rcases ht with rfl | rfl <;> norm_num at htag
  · have htag := congrArg (fun p : M => F nodeTag ![p]) h
    change F nodeTag ![pair tag payload+1] = F nodeTag ![pair (7 : M) a+1] at htag
    rw [nodeTag_model,nodeTag_model] at htag
    rcases ht with rfl | rfl <;> norm_num at htag

theorem internalQuantifierFree_binary_intro (root a b : M)
    (hr0 : root ≠ 0) (hnotAll : ∀ c : M, root ≠ ^∀ c) (hnotEx : ∀ c : M, root ≠ ^∃ c)
    (hedges : ∀ child bit : M, SourceDirectEdge root child bit → child = a ∨ child = b)
    (ha : InternalQuantifierFree a) (hb : InternalQuantifierFree b) : InternalQuantifierFree root := by
  intro ⟨c,h⟩
  rcases h with h | h
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^∀ c) hr0 (hnotAll c) h
    rcases hedges child bit he with rfl | rfl
    · exact ha ⟨c,Or.inl hd⟩
    · exact hb ⟨c,Or.inl hd⟩
  · obtain ⟨child,bit,he,hd⟩ := codedDescendant_firstEdge root (^∃ c) hr0 (hnotEx c) h
    rcases hedges child bit he with rfl | rfl
    · exact ha ⟨c,Or.inr hd⟩
    · exact hb ⟨c,Or.inr hd⟩

theorem internalQuantifierFree_and_iff (a b : M) :
    InternalQuantifierFree (a ^⋏ b) ↔ InternalQuantifierFree a ∧ InternalQuantifierFree b := by
  have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨internalQuantifierFree_child _ _ _ hl h,internalQuantifierFree_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply internalQuantifierFree_binary_intro (a ^⋏ b) a b
    · change pair (4 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).1
    · intro c; exact (binaryCode_not_binders 4 (pair a b) c (Or.inl rfl)).2
    · intro child bit he; exact directEdge_and_child a b child bit he
    · exact ha
    · exact hb

theorem internalQuantifierFree_or_iff (a b : M) :
    InternalQuantifierFree (a ^⋎ b) ↔ InternalQuantifierFree a ∧ InternalQuantifierFree b := by
  have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
  constructor
  · intro h; exact ⟨internalQuantifierFree_child _ _ _ hl h,internalQuantifierFree_child _ _ _ hr h⟩
  · rintro ⟨ha,hb⟩
    apply internalQuantifierFree_binary_intro (a ^⋎ b) a b
    · change pair (5 : M) (pair a b)+1 ≠ 0
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).1
    · intro c; exact (binaryCode_not_binders 5 (pair a b) c (Or.inr rfl)).2
    · intro child bit he; exact directEdge_or_child a b child bit he
    · exact ha
    · exact hb

/-- The exact seeded compiler field for every internally quantifier-free
formula in the source sequent. -/
theorem simRuleAllFresh_quantifierFreeSeed (reserve e s p q d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s p d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s) (hq : q ∈ s)
    (hqf : InternalQuantifierFree q) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalQuant.all (simBase e) (numericalTranslation.tr e q))) :=
  simRuleAllFresh_quantifierFree e s q _ hs hq (depthAdmission_ranked e _ ha.1) ha.2.2.1 hqf

#print axioms codedDescendant_firstEdge
#print axioms directEdge_and_child
#print axioms directEdge_or_child
#print axioms binaryCode_not_binders
#print axioms internalQuantifierFree_binary_intro
#print axioms internalQuantifierFree_and_iff
#print axioms internalQuantifierFree_or_iff
#print axioms simRuleAllFresh_quantifierFreeSeed
end models
end PA194ModelLogic
