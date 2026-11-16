import PA194ModelQFGeneralBase
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
local instance memQfZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance memQfOne : One M := ⟨F oneCode Fin.elim0⟩
local instance memQfAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance memQfMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance memQfLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance memQfIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- No internally reached equality atom or binder appears. -/
def InternalMembershipQF (p : M) : Prop :=
  InternalQuantifierFree p ∧
    ¬ ∃ v : M, CodedSyntacticDescendant p (^rel (2 : M) (0 : M) v) ∨
      CodedSyntacticDescendant p (^nrel (2 : M) (0 : M) v)

theorem internalMembershipQF_definable : 𝚷₁-Predicate (InternalMembershipQF : M → Prop) := by
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  haveI : 𝚺₁-Relation (CodedSyntacticDescendant (M := M)) := codedSyntacticDescendant_definable
  unfold InternalMembershipQF
  definability

theorem internalMembershipQF_child (parent child bit : M)
    (he : SourceDirectEdge parent child bit) (h : InternalMembershipQF parent) : InternalMembershipQF child := by
  refine ⟨internalQuantifierFree_child parent child bit he h.1,?_⟩
  intro ⟨v,hv⟩
  apply h.2
  refine ⟨v,?_⟩
  rcases hv with hv | hv
  · exact Or.inl (codedSyntacticDescendant_extend parent child (^rel (2 : M) (0 : M) v) bit he hv)
  · exact Or.inr (codedSyntacticDescendant_extend parent child (^nrel (2 : M) (0 : M) v) bit he hv)

theorem internalMembershipQF_relation_one (r v tag : M)
    (hr : SourceL.IsRel 2 r) (ht : tag = 0 ∨ tag = 1)
    (hq : InternalMembershipQF (if tag = 0 then ^rel (2 : M) r v else ^nrel (2 : M) r v)) : r = 1 := by
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with h | h
  · subst r
    apply False.elim
    apply hq.2
    refine ⟨v,?_⟩
    rcases ht with rfl | rfl
    · simp only [ite_true] at hq
      simpa only [ite_true] using (Or.inl (codedSyntacticDescendant_self (^rel (2 : M) (0 : M) v)) :
        CodedSyntacticDescendant (^rel (2 : M) (0 : M) v) (^rel (2 : M) (0 : M) v) ∨
          CodedSyntacticDescendant (^rel (2 : M) (0 : M) v) (^nrel (2 : M) (0 : M) v))
    · simp only [Arithmetic.one_ne_zero,ite_false] at hq
      simpa only [Arithmetic.one_ne_zero,ite_false] using (Or.inr (codedSyntacticDescendant_self (^nrel (2 : M) (0 : M) v)) :
        CodedSyntacticDescendant (^nrel (2 : M) (0 : M) v) (^rel (2 : M) (0 : M) v) ∨
          CodedSyntacticDescendant (^nrel (2 : M) (0 : M) v) (^nrel (2 : M) (0 : M) v))
  · exact h

/-- Both directions of target-formula transport under a fixed premise. -/
def TargetPremiseRewrite (E A B : M) : Prop :=
  TargetProvable (impValue E (impValue A B)) ∧ TargetProvable (impValue E (impValue B A))

theorem targetPremiseRewrite_refl (E A : M) : TargetPremiseRewrite E A A := by
  constructor <;> exact tp_mp (imp_refl A) (imp_k (impValue A A) E)

theorem targetPremiseRewrite_neg (E A B : M) (h : TargetPremiseRewrite E A B) :
    TargetPremiseRewrite E (negValue A) (negValue B) := by
  constructor
  · let he : Ctx [B,negValue A,E] E := .assumption (by simp)
    let hn : Ctx [B,negValue A,E] (negValue A) := .assumption (by simp)
    let hb : Ctx [B,negValue A,E] B := .assumption (by simp)
    let ha : Ctx [B,negValue A,E] A := .mp hb (.mp he (.closed h.2))
    exact (Ctx.mp ha hn).deduction.deduction.deduction.empty
  · let he : Ctx [A,negValue B,E] E := .assumption (by simp)
    let hn : Ctx [A,negValue B,E] (negValue B) := .assumption (by simp)
    let ha : Ctx [A,negValue B,E] A := .assumption (by simp)
    let hb : Ctx [A,negValue B,E] B := .mp ha (.mp he (.closed h.1))
    exact (Ctx.mp hb hn).deduction.deduction.deduction.empty

theorem targetPremiseRewrite_and (E A B C D : M)
    (h1 : TargetPremiseRewrite E A B) (h2 : TargetPremiseRewrite E C D) :
    TargetPremiseRewrite E (conjValue A C) (conjValue B D) := by
  constructor
  · let he : Ctx [conjValue A C,E] E := .assumption (by simp)
    let hh : Ctx [conjValue A C,E] (conjValue A C) := .assumption (by simp)
    exact (Ctx.andIntro (.mp hh.andLeft (.mp he (.closed h1.1)))
      (.mp hh.andRight (.mp he (.closed h2.1)))).deduction.deduction.empty
  · let he : Ctx [conjValue B D,E] E := .assumption (by simp)
    let hh : Ctx [conjValue B D,E] (conjValue B D) := .assumption (by simp)
    exact (Ctx.andIntro (.mp hh.andLeft (.mp he (.closed h1.2)))
      (.mp hh.andRight (.mp he (.closed h2.2)))).deduction.deduction.empty

theorem targetPremiseRewrite_imp (E A B C D : M)
    (h1 : TargetPremiseRewrite E A B) (h2 : TargetPremiseRewrite E C D) :
    TargetPremiseRewrite E (impValue A C) (impValue B D) := by
  constructor
  · let he : Ctx [B,impValue A C,E] E := .assumption (by simp)
    let hi : Ctx [B,impValue A C,E] (impValue A C) := .assumption (by simp)
    let hb : Ctx [B,impValue A C,E] B := .assumption (by simp)
    let ha : Ctx [B,impValue A C,E] A := .mp hb (.mp he (.closed h1.2))
    let hc : Ctx [B,impValue A C,E] C := .mp ha hi
    exact (Ctx.mp hc (.mp he (.closed h2.1))).deduction.deduction.deduction.empty
  · let he : Ctx [A,impValue B D,E] E := .assumption (by simp)
    let hi : Ctx [A,impValue B D,E] (impValue B D) := .assumption (by simp)
    let ha : Ctx [A,impValue B D,E] A := .assumption (by simp)
    let hb : Ctx [A,impValue B D,E] B := .mp ha (.mp he (.closed h1.1))
    let hd : Ctx [A,impValue B D,E] D := .mp hb hi
    exact (Ctx.mp hd (.mp he (.closed h2.2))).deduction.deduction.deduction.empty

/-- Primitive equality transports a source membership atom between two
binder-label environments, including either or both occurrences. -/
theorem membershipAtom_binderRewrite (a b x y bound free reserve : M)
    (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^rel (2 : M) (1 : M) ?[a,b],pair x bound+1,free,x+1,reserve])
      (F fixedFormulaTranslation ![^rel (2 : M) (1 : M) ?[a,b],pair y bound+1,free,y+1,reserve]) := by
  rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
    · rw [fixedTranslation_membershipBoundDiagonal,fixedTranslation_membershipBoundDiagonal]
      constructor
      · exact reverseAll_target .diagonal 0 y x
      · exact chiDirect_target .diagonal 0 y x
    · rw [fixedTranslation_membershipBoundLeft,fixedTranslation_membershipBoundLeft]
      exact ⟨reverseRight_target y x (free.[j]),memRight y x (free.[j])⟩
  · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
    · rw [fixedTranslation_membershipBoundRight,fixedTranslation_membershipBoundRight]
      exact ⟨reverseLeft_target y x (free.[i]),memLeft y x (free.[i])⟩
    · rw [fixedTranslation_membershipFree,fixedTranslation_membershipFree]
      exact targetPremiseRewrite_refl _ _

theorem negativeMembershipAtom_binderRewrite (a b x y bound free reserve : M)
    (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^nrel (2 : M) (1 : M) ?[a,b],pair x bound+1,free,x+1,reserve])
      (F fixedFormulaTranslation ![^nrel (2 : M) (1 : M) ?[a,b],pair y bound+1,free,y+1,reserve]) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv]
  exact targetPremiseRewrite_neg _ _ _ (membershipAtom_binderRewrite a b x y bound free reserve ha hb)

/-- Internal structural transport for every quantifier-free membership-only
body with one available bound variable. -/
theorem membershipQF_binderRewrite (p x y bound free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalMembershipQF p) :
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
  haveI : 𝚷₁-Predicate (InternalMembershipQF : M → Prop) := internalMembershipQF_definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalMembershipQF q → IsSemiformula SourceL 1 q →
      TargetPremiseRewrite E (positiveTranslation e q) (positiveTranslation e' q)) := by
    unfold TargetPremiseRewrite
    definability
  have hall : ∀ q, IsUFormula SourceL q → InternalMembershipQF q → IsSemiformula SourceL 1 q →
      TargetPremiseRewrite E (positiveTranslation e q) (positiveTranslation e' q) := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv hmem hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hr1 := internalMembershipQF_relation_one r v 0 hr (Or.inl rfl) (by simpa using hmem)
      subst r
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      dsimp only [e,e',E]
      rw [positiveTranslation_model,positiveTranslation_model]
      exact membershipAtom_binderRewrite a b x y bound free reserve ha hb
    · intro arity r v hr hv hmem hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hr1 := internalMembershipQF_relation_one r v 1 hr (Or.inr rfl) (by simpa using hmem)
      subst r
      obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
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
      have ih1 := iha (internalMembershipQF_child _ _ _ hleft hmem) hsa
      have ih2 := ihb (internalMembershipQF_child _ _ _ hright hmem) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_and a b _ _ _ _ hau hbu,
        fixedFormulaTranslation_and a b _ _ _ _ hau hbu]
      exact targetPremiseRewrite_and _ _ _ _ _ ih1 ih2
    · intro a b hau hbu iha ihb hmem hscope
      have hleft : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ih1 := iha (internalMembershipQF_child _ _ _ hleft hmem) hsa
      have ih2 := ihb (internalMembershipQF_child _ _ _ hright hmem) hsb
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

theorem singletonStack_avoids (head x : M) (hhead : head ≠ x) (hx : 0 ≠ x) :
    ∀ i : M, (pair head (0 : M)+1).[i] ≠ x := by
  intro i
  rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
  · rw [←adjoin_def,nth_adjoin_zero]
    exact hhead
  · rw [←adjoin_def,nth_adjoin_succ]
    simpa using hx

/-- Alpha conversion of a universal source body that is internally
quantifier-free and membership-only. -/
theorem membershipQF_allAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalMembershipQF p)
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
  have hrew := membershipQF_binderRewrite p x y 0 free reserve hp hqf
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

theorem membershipQF_allNegAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalMembershipQF p)
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
  have hrew := targetPremiseRewrite_neg _ _ _ (membershipQF_binderRewrite p x y 0 free reserve hp hqf)
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
theorem membershipQF_exAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalMembershipQF p)
    (hxy : x ≠ y) (hx0 : (0 : M) ≠ x) (hy0 : (0 : M) ≠ y)
    (hfx : ∀ i ≤ p, free.[i] ≠ x) (hfy : ∀ i ≤ p, free.[i] ≠ y)
    (hxz : x ≠ reserve) (hyz : y ≠ reserve) :
    TargetProvable (impValue
      (exValue x (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]))
      (exValue y (F fixedFormulaTranslation ![p,pair y (0 : M)+1,free,y+1,reserve]))) :=
  contrapose (membershipQF_allNegAlpha p y x free reserve hp hqf (Ne.symm hxy) hy0 hx0 hfy hfx hyz hxz)

/-- Exact seeded eigenlabel-vacuity field for a universal formula whose
body is internally quantifier-free and membership-only. -/
theorem simRuleAllFresh_allMembershipQFSeed (reserve e s introBody a d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s introBody d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ introBody) ∈ s) (hq : (^∀ a) ∈ s)
    (hqf : InternalMembershipQF a) :
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
  · exact membershipQF_allAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact membershipQF_allAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz

theorem simRuleAllFresh_exMembershipQFSeed (reserve e s introBody a d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s introBody d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ introBody) ∈ s) (hq : (^∃ a) ∈ s)
    (hqf : InternalMembershipQF a) :
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
  · exact membershipQF_exAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact membershipQF_exAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz

/-- The seeded universal-rule node leaves a full label of reserve slack. -/
theorem seedAdmission_allSlack (reserve e s introBody d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s introBody d)) :
    simBase e+1 < simReserve e := by
  let D := allIntro s introBody d
  have hrank : RankedAdmission e D := depthAdmission_ranked e D ha.1
  have hnode : (0 : M) < D := lt_of_le_of_lt zero_le (s_lt_allIntro s introBody d)
  have hnode1 : (1 : M) < D+1 := by simpa only [zero_add,add_comm] using add_lt_add_right hnode 1
  have hh : simBase e+1 < simBase e+(D+1) := by
    simpa only [add_comm] using add_lt_add_right hnode1 (simBase e)
  exact lt_of_lt_of_le hh hrank.2

theorem simRuleAllFresh_allMembershipQF_withSlack (e s a D : M)
    (hrank : RankedAdmission e D) (hb : simBound e = 0) (hres : simBase e+1 < simReserve e)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ a) ∈ s) (hqf : InternalMembershipQF a) :
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
  · exact membershipQF_allAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact membershipQF_allAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz


theorem simRuleAllFresh_exMembershipQF_withSlack (e s a D : M)
    (hrank : RankedAdmission e D) (hb : simBound e = 0) (hres : simBase e+1 < simReserve e)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ a) ∈ s) (hqf : InternalMembershipQF a) :
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
  · exact membershipQF_exAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact membershipQF_exAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz


#print axioms internalMembershipQF_definable
#print axioms internalMembershipQF_child
#print axioms internalMembershipQF_relation_one
#print axioms targetPremiseRewrite_refl
#print axioms targetPremiseRewrite_neg
#print axioms targetPremiseRewrite_and
#print axioms targetPremiseRewrite_imp
#print axioms membershipAtom_binderRewrite
#print axioms negativeMembershipAtom_binderRewrite
#print axioms membershipQF_binderRewrite
#print axioms singletonStack_avoids
#print axioms membershipQF_allAlpha
#print axioms membershipQF_allNegAlpha
#print axioms membershipQF_exAlpha
#print axioms simRuleAllFresh_allMembershipQFSeed
#print axioms simRuleAllFresh_exMembershipQFSeed
#print axioms seedAdmission_allSlack
#print axioms simRuleAllFresh_allMembershipQF_withSlack
#print axioms simRuleAllFresh_exMembershipQF_withSlack
end models
end PA194ModelLogic
