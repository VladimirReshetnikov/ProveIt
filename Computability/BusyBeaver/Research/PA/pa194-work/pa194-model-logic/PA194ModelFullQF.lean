import PA194ModelExAtomWitness
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
local instance fullQfZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance fullQfOne : One M := ⟨F oneCode Fin.elim0⟩
local instance fullQfAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance fullQfMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance fullQfLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance fullQfIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- The fixed reserved neighborhood label is fresh for both binder labels. -/
theorem equalityNeighborhoodLeftRewrite (x y a z : M) (hzy : z ≠ y) (hzx : z ≠ x) :
    TargetPremiseRewrite (eqValue y x) (neighborhoodValue x a z) (neighborhoodValue y a z) := by
  let E := eqValue y x
  let A := neighborhoodValue x a z
  let B := neighborhoodValue y a z
  let N := neighborhoodValue y x z
  have hn : TargetProvable (impValue E N) := primitiveToNeighborhood_target y x z hzy hzx
  constructor
  · let he : Ctx [A,E] E := .assumption (by simp)
    let ha : Ctx [A,E] A := .assumption (by simp)
    let hN : Ctx [A,E] N := .mp he (.closed hn)
    exact (Ctx.mp ha (.mp hN (.closed (neighborhood_trans y x a z)))).deduction.deduction.empty
  · let he : Ctx [B,E] E := .assumption (by simp)
    let hb : Ctx [B,E] B := .assumption (by simp)
    let hN : Ctx [B,E] N := .mp he (.closed hn)
    let hN' : Ctx [B,E] (neighborhoodValue x y z) := .mp hN (.closed (neighborhood_symm y x z))
    exact (Ctx.mp hb (.mp hN' (.closed (neighborhood_trans x y a z)))).deduction.deduction.empty

theorem equalityNeighborhoodRightRewrite (x y a z : M) (hzy : z ≠ y) (hzx : z ≠ x) :
    TargetPremiseRewrite (eqValue y x) (neighborhoodValue a x z) (neighborhoodValue a y z) := by
  let E := eqValue y x
  let A := neighborhoodValue a x z
  let B := neighborhoodValue a y z
  let N := neighborhoodValue y x z
  have hn : TargetProvable (impValue E N) := primitiveToNeighborhood_target y x z hzy hzx
  constructor
  · let he : Ctx [A,E] E := .assumption (by simp)
    let ha : Ctx [A,E] A := .assumption (by simp)
    let hN : Ctx [A,E] N := .mp he (.closed hn)
    let hN' : Ctx [A,E] (neighborhoodValue x y z) := .mp hN (.closed (neighborhood_symm y x z))
    exact (Ctx.mp hN' (.mp ha (.closed (neighborhood_trans a x y z)))).deduction.deduction.empty
  · let he : Ctx [B,E] E := .assumption (by simp)
    let hb : Ctx [B,E] B := .assumption (by simp)
    let hN : Ctx [B,E] N := .mp he (.closed hn)
    exact (Ctx.mp hN (.mp hb (.closed (neighborhood_trans a y x z)))).deduction.deduction.empty

theorem equalityAtom_binderRewrite (a b x y bound free reserve : M)
    (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b)
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[a,b],pair x bound+1,free,x+1,reserve])
      (F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[a,b],pair y bound+1,free,y+1,reserve]) := by
  rcases sourceSemitermOne_cases a ha with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
    · exact equalityDiagonal_binderRewrite _ x y bound free reserve ha
    · rw [fixedTranslation_equalityBoundLeft,fixedTranslation_equalityBoundLeft]
      exact equalityNeighborhoodLeftRewrite x y (free.[j]) reserve hzy hzx
  · rcases sourceSemitermOne_cases b hb with (rfl | ⟨j,rfl⟩)
    · rw [fixedTranslation_equalityBoundRight,fixedTranslation_equalityBoundRight]
      exact equalityNeighborhoodRightRewrite x y (free.[i]) reserve hzy hzx
    · exact equalityFree_binderRewrite i j x y bound free reserve

theorem negativeEqualityAtom_binderRewrite (a b x y bound free reserve : M)
    (ha : IsSemiterm SourceL 1 a) (hb : IsSemiterm SourceL 1 b)
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[a,b],pair x bound+1,free,x+1,reserve])
      (F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[a,b],pair y bound+1,free,y+1,reserve]) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv]
  exact targetPremiseRewrite_neg _ _ _ (equalityAtom_binderRewrite a b x y bound free reserve ha hb hzy hzx)

theorem fullQF_binderRewrite (p x y bound free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p)
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
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
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q → IsSemiformula SourceL 1 q →
      TargetPremiseRewrite E (positiveTranslation e q) (positiveTranslation e' q)) := by
    unfold TargetPremiseRewrite
    definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q → IsSemiformula SourceL 1 q →
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
      · obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
        obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
        dsimp only [e,e',E]
        rw [positiveTranslation_model,positiveTranslation_model]
        exact equalityAtom_binderRewrite a b x y bound free reserve ha hb hzy hzx
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
      · obtain ⟨a,b,hta,htb,rfl⟩ := IsUTermVec.two_iff.mp hv
        obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
        dsimp only [e,e',E]
        rw [positiveTranslation_model,positiveTranslation_model]
        exact negativeEqualityAtom_binderRewrite a b x y bound free reserve ha hb hzy hzx
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
      have ih1 := iha (internalQuantifierFree_child _ _ _ hleft hmem) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hright hmem) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_and a b _ _ _ _ hau hbu,
        fixedFormulaTranslation_and a b _ _ _ _ hau hbu]
      exact targetPremiseRewrite_and _ _ _ _ _ ih1 ih2
    · intro a b hau hbu iha ihb hmem hscope
      have hleft : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ih1 := iha (internalQuantifierFree_child _ _ _ hleft hmem) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hright hmem) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_or a b _ _ _ _ hau hbu,
        fixedFormulaTranslation_or a b _ _ _ _ hau hbu]
      exact targetPremiseRewrite_imp _ _ _ _ _ (targetPremiseRewrite_neg _ _ _ ih1) ih2
    · intro a hau ih hmem hscope
      exact False.elim (internalQuantifierFree_not_all a hmem)
    · intro a hau ih hmem hscope
      exact False.elim (internalQuantifierFree_not_ex a hmem)
  have h := hall p hp.isUFormula hqf hp
  dsimp only [e,e',E] at h
  simpa only [positiveTranslation_model] using h




theorem fullQF_allAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p)
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
  have hrew := fullQF_binderRewrite p x y 0 free reserve hp hqf (Ne.symm hyz) (Ne.symm hxz)
  have hboundY : ∀ i ≤ p, (pair y (0 : M)+1).[i] ≠ x := by
    intro i _; exact singletonStack_avoids y x (Ne.symm hxy) hx0 i
  have hvx := generalVacuity_below_all_codes x p (pair y (0 : M)+1) free common reserve
    hp.isUFormula hxc hboundY hfx hxz
  unfold GeneralVacuity at hvx
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvx
  have hnormY := quantifierFree_anyBases p (pair y (0 : M)+1) free (y+1) common reserve hp.isUFormula hqf
  rw [←hnormY] at hvx
  have hboundX : ∀ i ≤ p, (pair x (0 : M)+1).[i] ≠ y := by
    intro i _; exact singletonStack_avoids x y hxy hy0 i
  have hvy := generalVacuity_below_all_codes y p (pair x (0 : M)+1) free common reserve
    hp.isUFormula hyc hboundX hfy hyz
  unfold GeneralVacuity at hvy
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvy
  have hnormX := quantifierFree_anyBases p (pair x (0 : M)+1) free (x+1) common reserve hp.isUFormula hqf
  rw [←hnormX] at hvy
  have hs : TargetProvable (impValue (allValue x A) B) :=
    specializeWithMirroredEquality_target x y A B hvx hrew.1
  have hv : TargetProvable (impValue (allValue x A) (allValue y (allValue x A))) :=
    universalVacuity y x A hvy
  exact imp_trans hv (liftImp y hs)

theorem fullQF_allNegAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p)
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
  have hrew := targetPremiseRewrite_neg _ _ _ (fullQF_binderRewrite p x y 0 free reserve hp hqf (Ne.symm hyz) (Ne.symm hxz))
  have hboundY : ∀ i ≤ p, (pair y (0 : M)+1).[i] ≠ x := by
    intro i _; exact singletonStack_avoids y x (Ne.symm hxy) hx0 i
  have hvx := generalVacuity_below_all_codes x p (pair y (0 : M)+1) free common reserve
    hp.isUFormula hxc hboundY hfx hxz
  unfold GeneralVacuity at hvx
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvx
  have hnormY := quantifierFree_anyBases p (pair y (0 : M)+1) free (y+1) common reserve hp.isUFormula hqf
  rw [←hnormY] at hvx
  have hboundX : ∀ i ≤ p, (pair x (0 : M)+1).[i] ≠ y := by
    intro i _; exact singletonStack_avoids x y hxy hy0 i
  have hvy := generalVacuity_below_all_codes y p (pair x (0 : M)+1) free common reserve
    hp.isUFormula hyc hboundX hfy hyz
  unfold GeneralVacuity at hvy
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvy
  have hnormX := quantifierFree_anyBases p (pair x (0 : M)+1) free (x+1) common reserve hp.isUFormula hqf
  rw [←hnormX] at hvy
  have hvxNeg : TargetProvable (impValue B (allValue x B)) := negationVacuity x _ hvx
  have hvyNeg : TargetProvable (impValue A (allValue y A)) := negationVacuity y _ hvy
  have hs : TargetProvable (impValue (allValue x A) B) :=
    specializeWithMirroredEquality_target x y A B hvxNeg hrew.1
  have hv : TargetProvable (impValue (allValue x A) (allValue y (allValue x A))) :=
    universalVacuity y x A hvyNeg
  exact imp_trans hv (liftImp y hs)

/-- Existential alpha conversion follows from negative universal alpha. -/
theorem fullQF_exAlpha (p x y free reserve : M)
    (hp : IsSemiformula SourceL 1 p) (hqf : InternalQuantifierFree p)
    (hxy : x ≠ y) (hx0 : (0 : M) ≠ x) (hy0 : (0 : M) ≠ y)
    (hfx : ∀ i ≤ p, free.[i] ≠ x) (hfy : ∀ i ≤ p, free.[i] ≠ y)
    (hxz : x ≠ reserve) (hyz : y ≠ reserve) :
    TargetProvable (impValue
      (exValue x (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]))
      (exValue y (F fixedFormulaTranslation ![p,pair y (0 : M)+1,free,y+1,reserve]))) :=
  contrapose (fullQF_allNegAlpha p y x free reserve hp hqf (Ne.symm hxy) hy0 hx0 hfy hfx hyz hxz)

/-- Exact seeded eigenlabel-vacuity field for a universal formula whose
body is internally quantifier-free. -/
theorem simRuleAllFresh_allFullQFSeed (reserve e s introBody a d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s introBody d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ introBody) ∈ s) (hq : (^∀ a) ∈ s)
    (hqf : InternalQuantifierFree a) :
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
  · exact fullQF_allAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact fullQF_allAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz

theorem simRuleAllFresh_exFullQFSeed (reserve e s introBody a d : M)
    (ha : SeedAdmission 0 reserve e (allIntro s introBody d))
    (hs : IsFormulaSet SourceL s) (hm : (^∀ introBody) ∈ s) (hq : (^∃ a) ∈ s)
    (hqf : InternalQuantifierFree a) :
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
  · exact fullQF_exAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact fullQF_exAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz


theorem simRuleAllFresh_allFullQF_withSlack (e s a D : M)
    (hrank : RankedAdmission e D) (hb : simBound e = 0) (hres : simBase e+1 < simReserve e)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ a) ∈ s) (hqf : InternalQuantifierFree a) :
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
  · exact fullQF_allAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact fullQF_allAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz


theorem simRuleAllFresh_exFullQF_withSlack (e s a D : M)
    (hrank : RankedAdmission e D) (hb : simBound e = 0) (hres : simBase e+1 < simReserve e)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ a) ∈ s) (hqf : InternalQuantifierFree a) :
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
  · exact fullQF_exAlpha a (simBase e) (simBase e+1) (simFree e) (simReserve e)
      hbody hqf (ne_of_lt (lt_add_one _)) hx0 hy0 hfx hfy hxz hyz
  · exact fullQF_exAlpha a (simBase e+1) (simBase e) (simFree e) (simReserve e)
      hbody hqf (Ne.symm (ne_of_lt (lt_add_one _))) hy0 hx0 hfy hfx hyz hxz





#print axioms fullQF_allAlpha
#print axioms fullQF_allNegAlpha
#print axioms fullQF_exAlpha
#print axioms simRuleAllFresh_allFullQFSeed
#print axioms simRuleAllFresh_exFullQFSeed
#print axioms simRuleAllFresh_allFullQF_withSlack
#print axioms simRuleAllFresh_exFullQF_withSlack
#print axioms fullQF_binderRewrite
#print axioms equalityNeighborhoodLeftRewrite
#print axioms equalityNeighborhoodRightRewrite
#print axioms equalityAtom_binderRewrite
#print axioms negativeEqualityAtom_binderRewrite
end models
end PA194ModelLogic
