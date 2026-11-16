import PA194ModelMembershipQFRewrite
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
local instance reflQfZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance reflQfOne : One M := ⟨F oneCode Fin.elim0⟩
local instance reflQfAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance reflQfMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance reflQfLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance reflQfIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Equality atoms are permitted only when both coded term arguments agree. -/
def InternalReflexiveQF (p : M) : Prop :=
  InternalQuantifierFree p ∧
    ¬ ∃ v : M, v.[0] ≠ v.[1] ∧
      (CodedSyntacticDescendant p (^rel (2 : M) (0 : M) v) ∨
       CodedSyntacticDescendant p (^nrel (2 : M) (0 : M) v))

theorem internalReflexiveQF_definable : 𝚷₁-Predicate (InternalReflexiveQF : M → Prop) := by
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  haveI : 𝚺₁-Relation (CodedSyntacticDescendant (M := M)) := codedSyntacticDescendant_definable
  unfold InternalReflexiveQF
  definability

theorem internalReflexiveQF_child (parent child bit : M)
    (he : SourceDirectEdge parent child bit) (h : InternalReflexiveQF parent) : InternalReflexiveQF child := by
  refine ⟨internalQuantifierFree_child parent child bit he h.1,?_⟩
  intro ⟨v,hn,hv⟩
  apply h.2
  refine ⟨v,hn,?_⟩
  rcases hv with hv | hv
  · exact Or.inl (codedSyntacticDescendant_extend parent child (^rel (2 : M) (0 : M) v) bit he hv)
  · exact Or.inr (codedSyntacticDescendant_extend parent child (^nrel (2 : M) (0 : M) v) bit he hv)

theorem internalReflexiveQF_eq_arguments (v tag : M) (ht : tag = 0 ∨ tag = 1)
    (h : InternalReflexiveQF (if tag = 0 then ^rel (2 : M) (0 : M) v else ^nrel (2 : M) (0 : M) v)) :
    v.[0] = v.[1] := by
  by_contra hn
  apply h.2
  refine ⟨v,hn,?_⟩
  rcases ht with rfl | rfl
  · simpa only [ite_true] using (Or.inl (codedSyntacticDescendant_self (^rel (2 : M) (0 : M) v)) :
      CodedSyntacticDescendant (^rel (2 : M) (0 : M) v) (^rel (2 : M) (0 : M) v) ∨
      CodedSyntacticDescendant (^rel (2 : M) (0 : M) v) (^nrel (2 : M) (0 : M) v))
  · simpa only [Arithmetic.one_ne_zero,ite_false] using (Or.inr (codedSyntacticDescendant_self (^nrel (2 : M) (0 : M) v)) :
      CodedSyntacticDescendant (^nrel (2 : M) (0 : M) v) (^rel (2 : M) (0 : M) v) ∨
      CodedSyntacticDescendant (^nrel (2 : M) (0 : M) v) (^nrel (2 : M) (0 : M) v))

theorem targetPremiseRewrite_of_theorems (E A B : M) (ha : TargetProvable A) (hb : TargetProvable B) :
    TargetPremiseRewrite E A B := by
  constructor
  · let h : Ctx [A,E] B := .closed hb
    exact h.deduction.deduction.empty
  · let h : Ctx [B,E] A := .closed ha
    exact h.deduction.deduction.empty

theorem equalityDiagonal_binderRewrite (a x y bound free reserve : M)
    (ha : IsSemiterm SourceL 1 a) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[a,a],pair x bound+1,free,x+1,reserve])
      (F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[a,a],pair y bound+1,free,y+1,reserve]) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[a,a] : M) := by simp [ha.isUTerm]
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [ite_true,adjoin_def]
  rw [equalityAtom_model,equalityAtom_model]
  exact targetPremiseRewrite_of_theorems _ _ _ (neighborhood_refl _ _) (neighborhood_refl _ _)

theorem negativeEqualityDiagonal_binderRewrite (a x y bound free reserve : M)
    (ha : IsSemiterm SourceL 1 a) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[a,a],pair x bound+1,free,x+1,reserve])
      (F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[a,a],pair y bound+1,free,y+1,reserve]) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[a,a] : M) := by simp [ha.isUTerm]
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv]
  exact targetPremiseRewrite_neg _ _ _ (equalityDiagonal_binderRewrite a x y bound free reserve ha)

theorem reflexiveQF_binderRewrite (p x y bound free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalReflexiveQF p) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![p,pair x bound+1,free,x+1,reserve])
      (F fixedFormulaTranslation ![p,pair y bound+1,free,y+1,reserve]) := by
  let e := pair (pair x bound+1) (pair free (pair (x+1) reserve))
  let e' := pair (pair y bound+1) (pair free (pair (y+1) reserve))
  let E := eqValue y x
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₂ (impValue : M → M → M) := (numericalCalc (M := M)).imp_defined.to_definable
  haveI : 𝚺₁-Predicate (TargetProvable : M → Prop) := targetProvable_definable
  haveI : 𝚷₁-Predicate (InternalReflexiveQF : M → Prop) := internalReflexiveQF_definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalReflexiveQF q → IsSemiformula SourceL 1 q →
      TargetPremiseRewrite E (positiveTranslation e q) (positiveTranslation e' q)) := by
    unfold TargetPremiseRewrite
    definability
  have hall : ∀ q, IsUFormula SourceL q → InternalReflexiveQF q → IsSemiformula SourceL 1 q →
      TargetPremiseRewrite E (positiveTranslation e q) (positiveTranslation e' q) := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv hmem hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hr' : r = 0 ∨ r = 1 := by
        change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
        simpa using hr
      rcases hr' with rfl | rfl
      · have hab := internalReflexiveQF_eq_arguments v 0 (Or.inl rfl) (by simpa using hmem)
        obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
        have hval : a = b := by
          have h1 : (1 : M) = (0 : M)+1 := by simp
          rw [h1,nth_adjoin_zero,nth_adjoin_succ,nth_adjoin_zero] at hab
          exact hab
        subst b
        obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
        dsimp only [e,e',E]
        rw [positiveTranslation_model,positiveTranslation_model]
        exact equalityDiagonal_binderRewrite a x y bound free reserve ha
      · obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
        obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
        dsimp only [e,e',E]
        rw [positiveTranslation_model,positiveTranslation_model]
        exact membershipAtom_binderRewrite a b x y bound free reserve ha hb
    · intro arity r v hr hv hmem hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hr' : r = 0 ∨ r = 1 := by
        change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
        simpa using hr
      rcases hr' with rfl | rfl
      · have hab := internalReflexiveQF_eq_arguments v 1 (Or.inr rfl) (by simpa using hmem)
        obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
        have hval : a = b := by
          have h1 : (1 : M) = (0 : M)+1 := by simp
          rw [h1,nth_adjoin_zero,nth_adjoin_succ,nth_adjoin_zero] at hab
          exact hab
        subst b
        obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
        dsimp only [e,e',E]
        rw [positiveTranslation_model,positiveTranslation_model]
        exact negativeEqualityDiagonal_binderRewrite a x y bound free reserve ha
      · obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
        obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
        dsimp only [e,e',E]
        rw [positiveTranslation_model,positiveTranslation_model]
        exact negativeMembershipAtom_binderRewrite a b x y bound free reserve ha hb
    · intro _ _
      dsimp only [e,e',E]
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
      exact targetPremiseRewrite_refl _ _
    · intro _ _
      dsimp only [e,e',E]
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
      exact targetPremiseRewrite_refl _ _
    · intro a b hau hbu iha ihb hmem hscope
      have hleft : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hscope
      have ih1 := iha (internalReflexiveQF_child _ _ _ hleft hmem) hsa
      have ih2 := ihb (internalReflexiveQF_child _ _ _ hright hmem) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_and a b _ _ _ _ hau hbu,
        fixedFormulaTranslation_and a b _ _ _ _ hau hbu]
      exact targetPremiseRewrite_and _ _ _ _ _ ih1 ih2
    · intro a b hau hbu iha ihb hmem hscope
      have hleft : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ih1 := iha (internalReflexiveQF_child _ _ _ hleft hmem) hsa
      have ih2 := ihb (internalReflexiveQF_child _ _ _ hright hmem) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_or a b _ _ _ _ hau hbu,
        fixedFormulaTranslation_or a b _ _ _ _ hau hbu]
      exact targetPremiseRewrite_imp _ _ _ _ _ (targetPremiseRewrite_neg _ _ _ ih1) ih2
    · intro a hau ih hmem hscope
      exact False.elim (internalQuantifierFree_not_all a hmem.1)
    · intro a hau ih hmem hscope
      exact False.elim (internalQuantifierFree_not_ex a hmem.1)
  have h := hall p hp.isUFormula hqf hp
  dsimp only [e,e',E] at h
  simpa only [positiveTranslation_model] using h


theorem reflexiveQF_allAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalReflexiveQF p)
    (hxy : x ≠ y) (hx0 : (0 : M) ≠ x) (hy0 : (0 : M) ≠ y)
    (hfx : ∀ i ≤ p, free.[i] ≠ x) (hfy : ∀ i ≤ p, free.[i] ≠ y)
    (hxz : x ≠ reserve) (hyz : y ≠ reserve) :
    TargetProvable (impValue
      (allValue x (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]))
      (allValue y (F fixedFormulaTranslation ![p,pair y (0 : M)+1,free,y+1,reserve]))) := by
  let A := F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]
  let B := F fixedFormulaTranslation ![p,pair y (0 : M)+1,free,y+1,reserve]
  let common := x+y+1
  have hxc : x < common := by
    exact lt_of_le_of_lt (show x ≤ x+y from le_self_add) (lt_add_one _)
  have hyc : y < common := by
    have hy : y ≤ x+y := by simpa only [add_comm] using (show y ≤ y+x from le_self_add)
    exact lt_of_le_of_lt hy (lt_add_one _)
  have hrew := reflexiveQF_binderRewrite p x y 0 free reserve hp hqf
  have hboundY : ∀ i ≤ p, (pair y (0 : M)+1).[i] ≠ x := by
    intro i _; exact singletonStack_avoids y x (Ne.symm hxy) hx0 i
  have hvx := generalVacuity_below_all_codes x p (pair y (0 : M)+1) free common reserve
    hp.isUFormula hxc hboundY hfx hxz
  unfold GeneralVacuity at hvx
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvx
  have hnormY := quantifierFree_anyBases p (pair y (0 : M)+1) free (y+1) common reserve hp.isUFormula hqf.1
  rw [←hnormY] at hvx
  have hboundX : ∀ i ≤ p, (pair x (0 : M)+1).[i] ≠ y := by
    intro i _; exact singletonStack_avoids x y hxy hy0 i
  have hvy := generalVacuity_below_all_codes y p (pair x (0 : M)+1) free common reserve
    hp.isUFormula hyc hboundX hfy hyz
  unfold GeneralVacuity at hvy
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvy
  have hnormX := quantifierFree_anyBases p (pair x (0 : M)+1) free (x+1) common reserve hp.isUFormula hqf.1
  rw [←hnormX] at hvy
  have hs : TargetProvable (impValue (allValue x A) B) :=
    specializeWithMirroredEquality_target x y A B hvx hrew.1
  have hv : TargetProvable (impValue (allValue x A) (allValue y (allValue x A))) :=
    universalVacuity y x A hvy
  exact imp_trans hv (liftImp y hs)

theorem reflexiveQF_allNegAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalReflexiveQF p)
    (hxy : x ≠ y) (hx0 : (0 : M) ≠ x) (hy0 : (0 : M) ≠ y)
    (hfx : ∀ i ≤ p, free.[i] ≠ x) (hfy : ∀ i ≤ p, free.[i] ≠ y)
    (hxz : x ≠ reserve) (hyz : y ≠ reserve) :
    TargetProvable (impValue
      (allValue x (negValue (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve])))
      (allValue y (negValue (F fixedFormulaTranslation ![p,pair y (0 : M)+1,free,y+1,reserve])))) := by
  let A := negValue (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve])
  let B := negValue (F fixedFormulaTranslation ![p,pair y (0 : M)+1,free,y+1,reserve])
  let common := x+y+1
  have hxc : x < common := by
    exact lt_of_le_of_lt (show x ≤ x+y from le_self_add) (lt_add_one _)
  have hyc : y < common := by
    have hy : y ≤ x+y := by simpa only [add_comm] using (show y ≤ y+x from le_self_add)
    exact lt_of_le_of_lt hy (lt_add_one _)
  have hrew := targetPremiseRewrite_neg _ _ _ (reflexiveQF_binderRewrite p x y 0 free reserve hp hqf)
  have hboundY : ∀ i ≤ p, (pair y (0 : M)+1).[i] ≠ x := by
    intro i _; exact singletonStack_avoids y x (Ne.symm hxy) hx0 i
  have hvx := generalVacuity_below_all_codes x p (pair y (0 : M)+1) free common reserve
    hp.isUFormula hxc hboundY hfx hxz
  unfold GeneralVacuity at hvx
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvx
  have hnormY := quantifierFree_anyBases p (pair y (0 : M)+1) free (y+1) common reserve hp.isUFormula hqf.1
  rw [←hnormY] at hvx
  have hboundX : ∀ i ≤ p, (pair x (0 : M)+1).[i] ≠ y := by
    intro i _; exact singletonStack_avoids x y hxy hy0 i
  have hvy := generalVacuity_below_all_codes y p (pair x (0 : M)+1) free common reserve
    hp.isUFormula hyc hboundX hfy hyz
  unfold GeneralVacuity at hvy
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvy
  have hnormX := quantifierFree_anyBases p (pair x (0 : M)+1) free (x+1) common reserve hp.isUFormula hqf.1
  rw [←hnormX] at hvy
  have hvxNeg : TargetProvable (impValue B (allValue x B)) := negationVacuity x _ hvx
  have hvyNeg : TargetProvable (impValue A (allValue y A)) := negationVacuity y _ hvy
  have hs : TargetProvable (impValue (allValue x A) B) :=
    specializeWithMirroredEquality_target x y A B hvxNeg hrew.1
  have hv : TargetProvable (impValue (allValue x A) (allValue y (allValue x A))) :=
    universalVacuity y x A hvyNeg
  exact imp_trans hv (liftImp y hs)

/-- Existential alpha conversion follows from negative universal alpha. -/
theorem reflexiveQF_exAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalReflexiveQF p)
    (hxy : x ≠ y) (hx0 : (0 : M) ≠ x) (hy0 : (0 : M) ≠ y)
    (hfx : ∀ i ≤ p, free.[i] ≠ x) (hfy : ∀ i ≤ p, free.[i] ≠ y)
    (hxz : x ≠ reserve) (hyz : y ≠ reserve) :
    TargetProvable (impValue
      (exValue x (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]))
      (exValue y (F fixedFormulaTranslation ![p,pair y (0 : M)+1,free,y+1,reserve]))) :=
  contrapose (reflexiveQF_allNegAlpha p y x free reserve hp hqf (Ne.symm hxy) hy0 hx0 hfy hfx hyz hxz)

/-- Exact seeded eigenlabel-vacuity field for a universal formula whose
body is internally quantifier-free with membership or reflexive-equality atoms. -/
theorem simRuleAllFresh_allReflexiveQFSeed (reserve e s introBody a d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s introBody d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ introBody) ∈ s) (hq : (^∀ a) ∈ s)
    (hqf : InternalReflexiveQF a) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∀ a))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∀ a)))) := by
  let D := allIntro s introBody d
  have hrank : RankedAdmission e D := depthAdmission_ranked e D ha.1
  have hb : simBound e = 0 := ha.2.2.1
  have hbody : IsSemiformula SourceL 1 a := by
    have hf := hs _ hq
    simpa only [IsSemiformula.all,zero_add] using hf
  have hpos : (0 : M) < simBase e := lt_of_le_of_lt zero_le (rankedEnvironment_free_lt e 0 hrank.1)
  have hnode : (0 : M) < D := lt_of_le_of_lt zero_le (s_lt_allIntro s introBody d)
  have hnode1 : (1 : M) < D+1 := by simpa only [zero_add,add_comm] using add_lt_add_right hnode 1
  have hres : simBase e+1 < simReserve e := by
    have hh : simBase e+1 < simBase e+(D+1) := by
      simpa only [add_comm] using add_lt_add_right hnode1 (simBase e)
    exact lt_of_lt_of_le hh hrank.2
  have hx0 : (0 : M) ≠ simBase e := ne_of_lt hpos
  have hy0 : (0 : M) ≠ simBase e+1 := ne_of_lt (lt_trans hpos (lt_add_one _))
  have hfx : ∀ i ≤ a, (simFree e).[i] ≠ simBase e := by
    intro i _; exact ne_of_lt (rankedEnvironment_free_lt e i hrank.1)
  have hfy : ∀ i ≤ a, (simFree e).[i] ≠ simBase e+1 := by
    intro i _; exact ne_of_lt (lt_trans (rankedEnvironment_free_lt e i hrank.1) (lt_add_one _))
  have hxz : simBase e ≠ simReserve e := ne_of_lt (lt_trans (lt_add_one _) hres)
  have hyz : simBase e+1 ≠ simReserve e := ne_of_lt hres
  apply simRuleAllFresh_of_baseShift e s (^∀ a) D hs hq hrank hb
  all_goals
    rw [fixedFormulaTranslation_all a _ _ _ _ hbody.isUFormula,
      fixedFormulaTranslation_all a _ _ _ _ hbody.isUFormula,hb]
  · exact reflexiveQF_allAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact reflexiveQF_allAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz

theorem simRuleAllFresh_exReflexiveQFSeed (reserve e s introBody a d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s introBody d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ introBody) ∈ s) (hq : (^∃ a) ∈ s)
    (hqf : InternalReflexiveQF a) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∃ a))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∃ a)))) := by
  let D := allIntro s introBody d
  have hrank : RankedAdmission e D := depthAdmission_ranked e D ha.1
  have hb : simBound e = 0 := ha.2.2.1
  have hbody : IsSemiformula SourceL 1 a := by
    have hf := hs _ hq
    simpa only [IsSemiformula.exs,zero_add] using hf
  have hpos : (0 : M) < simBase e := lt_of_le_of_lt zero_le (rankedEnvironment_free_lt e 0 hrank.1)
  have hnode : (0 : M) < D := lt_of_le_of_lt zero_le (s_lt_allIntro s introBody d)
  have hnode1 : (1 : M) < D+1 := by simpa only [zero_add,add_comm] using add_lt_add_right hnode 1
  have hres : simBase e+1 < simReserve e := by
    have hh : simBase e+1 < simBase e+(D+1) := by
      simpa only [add_comm] using add_lt_add_right hnode1 (simBase e)
    exact lt_of_lt_of_le hh hrank.2
  have hx0 : (0 : M) ≠ simBase e := ne_of_lt hpos
  have hy0 : (0 : M) ≠ simBase e+1 := ne_of_lt (lt_trans hpos (lt_add_one _))
  have hfx : ∀ i ≤ a, (simFree e).[i] ≠ simBase e := by
    intro i _; exact ne_of_lt (rankedEnvironment_free_lt e i hrank.1)
  have hfy : ∀ i ≤ a, (simFree e).[i] ≠ simBase e+1 := by
    intro i _; exact ne_of_lt (lt_trans (rankedEnvironment_free_lt e i hrank.1) (lt_add_one _))
  have hxz : simBase e ≠ simReserve e := ne_of_lt (lt_trans (lt_add_one _) hres)
  have hyz : simBase e+1 ≠ simReserve e := ne_of_lt hres
  apply simRuleAllFresh_of_baseShift e s (^∃ a) D hs hq hrank hb
  all_goals
    rw [fixedFormulaTranslation_ex a _ _ _ _ hbody.isUFormula,
      fixedFormulaTranslation_ex a _ _ _ _ hbody.isUFormula,hb]
  · exact reflexiveQF_exAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact reflexiveQF_exAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz


theorem simRuleAllFresh_allReflexiveQF_withSlack (e s a D : M)
    (hrank : RankedAdmission e D) (hb : simBound e = 0) (hres : simBase e+1 < simReserve e)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ a) ∈ s) (hqf : InternalReflexiveQF a) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∀ a))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∀ a)))) := by
  have hbody : IsSemiformula SourceL 1 a := by
    have hf := hs _ hq
    simpa only [IsSemiformula.all,zero_add] using hf
  have hpos : (0 : M) < simBase e := lt_of_le_of_lt zero_le (rankedEnvironment_free_lt e 0 hrank.1)
  have hx0 : (0 : M) ≠ simBase e := ne_of_lt hpos
  have hy0 : (0 : M) ≠ simBase e+1 := ne_of_lt (lt_trans hpos (lt_add_one _))
  have hfx : ∀ i ≤ a, (simFree e).[i] ≠ simBase e := by
    intro i _; exact ne_of_lt (rankedEnvironment_free_lt e i hrank.1)
  have hfy : ∀ i ≤ a, (simFree e).[i] ≠ simBase e+1 := by
    intro i _; exact ne_of_lt (lt_trans (rankedEnvironment_free_lt e i hrank.1) (lt_add_one _))
  have hxz : simBase e ≠ simReserve e := ne_of_lt (lt_trans (lt_add_one _) hres)
  have hyz : simBase e+1 ≠ simReserve e := ne_of_lt hres
  apply simRuleAllFresh_of_baseShift e s (^∀ a) D hs hq hrank hb
  all_goals
    rw [fixedFormulaTranslation_all a _ _ _ _ hbody.isUFormula,
      fixedFormulaTranslation_all a _ _ _ _ hbody.isUFormula,hb]
  · exact reflexiveQF_allAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact reflexiveQF_allAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz


theorem simRuleAllFresh_exReflexiveQF_withSlack (e s a D : M)
    (hrank : RankedAdmission e D) (hb : simBound e = 0) (hres : simBase e+1 < simReserve e)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ a) ∈ s) (hqf : InternalReflexiveQF a) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∃ a))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∃ a)))) := by
  have hbody : IsSemiformula SourceL 1 a := by
    have hf := hs _ hq
    simpa only [IsSemiformula.exs,zero_add] using hf
  have hpos : (0 : M) < simBase e := lt_of_le_of_lt zero_le (rankedEnvironment_free_lt e 0 hrank.1)
  have hx0 : (0 : M) ≠ simBase e := ne_of_lt hpos
  have hy0 : (0 : M) ≠ simBase e+1 := ne_of_lt (lt_trans hpos (lt_add_one _))
  have hfx : ∀ i ≤ a, (simFree e).[i] ≠ simBase e := by
    intro i _; exact ne_of_lt (rankedEnvironment_free_lt e i hrank.1)
  have hfy : ∀ i ≤ a, (simFree e).[i] ≠ simBase e+1 := by
    intro i _; exact ne_of_lt (lt_trans (rankedEnvironment_free_lt e i hrank.1) (lt_add_one _))
  have hxz : simBase e ≠ simReserve e := ne_of_lt (lt_trans (lt_add_one _) hres)
  have hyz : simBase e+1 ≠ simReserve e := ne_of_lt hres
  apply simRuleAllFresh_of_baseShift e s (^∃ a) D hs hq hrank hb
  all_goals
    rw [fixedFormulaTranslation_ex a _ _ _ _ hbody.isUFormula,
      fixedFormulaTranslation_ex a _ _ _ _ hbody.isUFormula,hb]
  · exact reflexiveQF_exAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact reflexiveQF_exAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz



#print axioms simRuleAllFresh_allReflexiveQF_withSlack
#print axioms simRuleAllFresh_exReflexiveQF_withSlack
#print axioms reflexiveQF_allAlpha
#print axioms reflexiveQF_allNegAlpha
#print axioms reflexiveQF_exAlpha
#print axioms simRuleAllFresh_allReflexiveQFSeed
#print axioms simRuleAllFresh_exReflexiveQFSeed
#print axioms reflexiveQF_binderRewrite
#print axioms equalityDiagonal_binderRewrite
#print axioms negativeEqualityDiagonal_binderRewrite
#print axioms internalReflexiveQF_definable
#print axioms internalReflexiveQF_child
#print axioms internalReflexiveQF_eq_arguments
end models
end PA194ModelLogic
