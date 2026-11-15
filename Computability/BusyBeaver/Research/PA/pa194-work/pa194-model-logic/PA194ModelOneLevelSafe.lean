import PA194ModelSafeQF
import PA194ModelOneLevelReflexive
import PA194ModelOneLevelFresh
import PA194ModelShallowFresh
import PA194ModelSeedEnvironment
import PA194ModelQFConverse
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
local instance oneSafeZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance oneSafeOne : One M := ⟨F oneCode Fin.elim0⟩
local instance oneSafeAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance oneSafeMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance oneSafeLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance oneSafeIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]









/-- Every reachable binder has a quantifier-free body with membership or reflexive equality atoms. -/
def OneLevelSafe (p : M) : Prop :=
  ¬ ∃ a : M, (CodedSyntacticDescendant p (^∀ a) ∨ CodedSyntacticDescendant p (^∃ a)) ∧
    ¬ InternalSafeQF a

theorem oneLevelSafe_definable : 𝚷₁-Predicate (OneLevelSafe : M → Prop) := by
  haveI : 𝚺₁-Relation (CodedSyntacticDescendant (M := M)) := codedSyntacticDescendant_definable
  haveI : 𝚷₁-Predicate (InternalSafeQF : M → Prop) := internalSafeQF_definable
  unfold OneLevelSafe
  definability

theorem oneLevelSafe_child (parent child bit : M)
    (he : SourceDirectEdge parent child bit) (h : OneLevelSafe parent) : OneLevelSafe child := by
  intro ⟨a,ha,hbad⟩
  apply h
  refine ⟨a,?_,hbad⟩
  rcases ha with ha | ha
  · exact Or.inl (codedSyntacticDescendant_extend parent child (^∀ a) bit he ha)
  · exact Or.inr (codedSyntacticDescendant_extend parent child (^∃ a) bit he ha)

theorem oneLevelSafe_all_body (a : M) (h : OneLevelSafe (^∀ a)) : InternalSafeQF a := by
  by_contra hn
  exact h ⟨a,Or.inl (codedSyntacticDescendant_self _),hn⟩

theorem oneLevelSafe_ex_body (a : M) (h : OneLevelSafe (^∃ a)) : InternalSafeQF a := by
  by_contra hn
  exact h ⟨a,Or.inr (codedSyntacticDescendant_self _),hn⟩

theorem oneLevelSafeFresh_all_codes (e p d : M) (hp : IsFormula SourceL p)
    (hsh : OneLevelSafe p) (ha : RankedAdmission e d) (hb : simBound e = 0)
    (hslack : simBase e+1 < simReserve e) : FreshBridge e p := by
  haveI : 𝚷₁-Predicate (OneLevelSafe : M → Prop) := oneLevelSafe_definable
  haveI : 𝚺₁-Predicate (FreshBridge (M := M) e) := freshBridge_definable e
  have hdef : 𝚺₁-Predicate (fun q : M => OneLevelSafe q → IsFormula SourceL q → FreshBridge e q) := by
    definability
  have hall : ∀ q, IsUFormula SourceL q → OneLevelSafe q → IsFormula SourceL q → FreshBridge e q := by
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
        (iha (oneLevelSafe_child _ _ _ hleft hsh) hfa)
        (ihb (oneLevelSafe_child _ _ _ hright hsh) hfb)
    · intro a b hau hbu iha ihb hsh hform
      have hleft : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hfa,hfb⟩ := IsSemiformula.or.mp hform
      exact freshBridge_or e a b hau hbu
        (iha (oneLevelSafe_child _ _ _ hleft hsh) hfa)
        (ihb (oneLevelSafe_child _ _ _ hright hsh) hfb)
    · intro a hau ih hsh hform
      have hqf := oneLevelSafe_all_body a hsh
      have hs : IsFormulaSet SourceL ({^∀ a} : M) := singletonFormulaSet _ hform
      have hm : (^∀ a) ∈ ({^∀ a} : M) := mem_singleton_iff.mpr rfl
      exact simRuleAllFresh_allSafeQF_withSlack e _ a d ha hb hslack hs hm hqf
    · intro a hau ih hsh hform
      have hqf := oneLevelSafe_ex_body a hsh
      have hs : IsFormulaSet SourceL ({^∃ a} : M) := singletonFormulaSet _ hform
      have hm : (^∃ a) ∈ ({^∃ a} : M) := mem_singleton_iff.mpr rfl
      exact simRuleAllFresh_exSafeQF_withSlack e _ a d ha hb hslack hs hm hqf
  exact hall p hp.isUFormula hsh hp

/-- Exact seeded field for arbitrary Boolean structure around one-level
quantifiers with quantifier-free bodies satisfying the safe-atom condition. -/
theorem simRuleAllFresh_oneLevelSafeSeed (reserve e s p q d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s p d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s) (hq : q ∈ s)
    (hlevel : OneLevelSafe q) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalQuant.all (simBase e) (numericalTranslation.tr e q))) :=
  oneLevelSafeFresh_all_codes e q _ (hs _ hq) hlevel (depthAdmission_ranked e _ ha.1) ha.2.2.1
    (seedAdmission_allSlack reserve e s p d ha)

theorem internalReflexiveQF_implies_safe (p : M)
    (h : InternalReflexiveQF p) : InternalSafeQF p := by
  refine ⟨h.1,?_⟩
  intro ⟨v,hn,_,hv⟩
  exact h.2 ⟨v,hn,hv⟩

theorem oneLevelReflexive_implies_safe (p : M)
    (h : OneLevelReflexive p) : OneLevelSafe p := by
  intro ⟨a,ha,hbad⟩
  apply hbad
  exact internalReflexiveQF_implies_safe a (by
    by_contra hmem
    exact h ⟨a,ha,hmem⟩)

#print axioms internalReflexiveQF_implies_safe
#print axioms oneLevelReflexive_implies_safe
#print axioms oneLevelSafe_definable
#print axioms oneLevelSafe_child
#print axioms oneLevelSafe_all_body
#print axioms oneLevelSafe_ex_body
#print axioms oneLevelSafeFresh_all_codes
#print axioms simRuleAllFresh_oneLevelSafeSeed
end models
end PA194ModelLogic
