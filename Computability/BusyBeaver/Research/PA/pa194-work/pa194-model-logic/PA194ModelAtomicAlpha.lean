import PA194ModelExNegativeMembership
import PA194ModelBelowFreshInduction
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
local instance atomAlphaZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance atomAlphaOne : One M := ⟨F oneCode Fin.elim0⟩
local instance atomAlphaAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance atomAlphaMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance atomAlphaLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance atomAlphaIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]







/-- One-way alpha conversion of a universal membership atom at fresh labels. -/
theorem targetMembershipAllAlphaRight (x y a : M)
    (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (allValue x (memValue a x)) (allValue y (memValue a y))) := by
  have hs : TargetProvable (impValue (allValue x (memValue a x)) (memValue a y)) :=
    specializeWithMirroredEquality_target x y _ _
      (membershipVacuity_target a y x hxa hxy) (reverseRight_target y x a)
  have hv : TargetProvable (impValue (allValue x (memValue a x))
      (allValue y (allValue x (memValue a x)))) :=
    universalVacuity y x _ (membershipVacuity_target a x y hya (Ne.symm hxy))
  exact imp_trans hv (liftImp y hs)

theorem targetMembershipAllAlphaLeft (x y a : M)
    (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (allValue x (memValue x a)) (allValue y (memValue y a))) := by
  have hs : TargetProvable (impValue (allValue x (memValue x a)) (memValue y a)) :=
    specializeWithMirroredEquality_target x y _ _
      (membershipVacuity_target y a x hxy hxa) (reverseLeft_target y x a)
  have hv : TargetProvable (impValue (allValue x (memValue x a))
      (allValue y (allValue x (memValue x a)))) :=
    universalVacuity y x _ (membershipVacuity_target x a y (Ne.symm hxy) hya)
  exact imp_trans hv (liftImp y hs)

theorem targetMembershipAllAlphaDiagonal (x y : M) (hxy : x ≠ y) :
    TargetProvable (impValue (allValue x (memValue x x)) (allValue y (memValue y y))) := by
  have hr : TargetProvable (impValue (eqValue y x) (impValue (memValue x x) (memValue y y))) := by
    let he : Ctx [memValue x x,eqValue y x] (eqValue y x) := .assumption (by simp)
    let hm : Ctx [memValue x x,eqValue y x] (memValue x x) := .assumption (by simp)
    let h1 : Ctx [memValue x x,eqValue y x] (memValue y x) := .mp hm (.mp he (.closed (reverseLeft_target y x x)))
    let h2 : Ctx [memValue x x,eqValue y x] (memValue y y) := .mp h1 (.mp he (.closed (reverseRight_target y x y)))
    exact h2.deduction.deduction.empty
  have hs : TargetProvable (impValue (allValue x (memValue x x)) (memValue y y)) :=
    specializeWithMirroredEquality_target x y _ _ (membershipVacuity_target y y x hxy hxy) hr
  have hv : TargetProvable (impValue (allValue x (memValue x x))
      (allValue y (allValue x (memValue x x)))) :=
    universalVacuity y x _ (membershipVacuity_target x x y (Ne.symm hxy) (Ne.symm hxy))
  exact imp_trans hv (liftImp y hs)

theorem targetNegMembershipAllAlphaRight (x y a : M)
    (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (allValue x (negValue (memValue a x)))
      (allValue y (negValue (memValue a y)))) := by
  let P := memValue a x
  let Q := memValue a y
  have hr : TargetProvable (impValue (eqValue y x) (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,eqValue y x] (eqValue y x) := .assumption (by simp)
    let hn : Ctx [Q,negValue P,eqValue y x] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,eqValue y x] Q := .assumption (by simp)
    let hp : Ctx [Q,negValue P,eqValue y x] P := .mp hq (.mp he (.closed (memRight y x a)))
    exact (Ctx.mp hp hn).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x y (negValue P) (negValue Q)
    (negationVacuity x Q (membershipVacuity_target a y x hxa hxy)) hr
  have hv := universalVacuity y x (negValue P)
    (negationVacuity y P (membershipVacuity_target a x y hya (Ne.symm hxy)))
  exact imp_trans hv (liftImp y hs)

theorem targetNegMembershipAllAlphaLeft (x y a : M)
    (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (allValue x (negValue (memValue x a)))
      (allValue y (negValue (memValue y a)))) := by
  let P := memValue x a
  let Q := memValue y a
  have hr : TargetProvable (impValue (eqValue y x) (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,eqValue y x] (eqValue y x) := .assumption (by simp)
    let hn : Ctx [Q,negValue P,eqValue y x] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,eqValue y x] Q := .assumption (by simp)
    let hp : Ctx [Q,negValue P,eqValue y x] P := .mp hq (.mp he (.closed (memLeft y x a)))
    exact (Ctx.mp hp hn).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x y (negValue P) (negValue Q)
    (negationVacuity x Q (membershipVacuity_target y a x hxy hxa)) hr
  have hv := universalVacuity y x (negValue P)
    (negationVacuity y P (membershipVacuity_target x a y (Ne.symm hxy) hya))
  exact imp_trans hv (liftImp y hs)

theorem targetNegMembershipAllAlphaDiagonal (x y : M) (hxy : x ≠ y) :
    TargetProvable (impValue (allValue x (negValue (memValue x x)))
      (allValue y (negValue (memValue y y)))) := by
  let P := memValue x x
  let Q := memValue y y
  have hr : TargetProvable (impValue (eqValue y x) (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,eqValue y x] (eqValue y x) := .assumption (by simp)
    let hn : Ctx [Q,negValue P,eqValue y x] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,eqValue y x] Q := .assumption (by simp)
    let h1 : Ctx [Q,negValue P,eqValue y x] (memValue x y) := .mp hq (.mp he (.closed (memLeft y x y)))
    let hp : Ctx [Q,negValue P,eqValue y x] P := .mp h1 (.mp he (.closed (memRight y x x)))
    exact (Ctx.mp hp hn).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x y (negValue P) (negValue Q)
    (negationVacuity x Q (membershipVacuity_target y y x hxy hxy)) hr
  have hv := universalVacuity y x (negValue P)
    (negationVacuity y P (membershipVacuity_target x x y (Ne.symm hxy) (Ne.symm hxy)))
  exact imp_trans hv (liftImp y hs)

/-- A genuinely quantified source formula in the actual `ruleAllFresh`
field, for arbitrary model-valued free-variable index. -/
theorem simRuleAllFresh_allMembershipBoundLeft (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]))))) := by
  let q : M := ^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_membershipBoundLeft,fixedTranslation_membershipBoundLeft]
  · apply targetMembershipAllAlphaRight
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetMembershipAllAlphaRight
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)


theorem simRuleAllFresh_allMembershipBoundRight (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))))) := by
  let q : M := ^∀ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_membershipBoundRight,fixedTranslation_membershipBoundRight]
  · apply targetMembershipAllAlphaLeft
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetMembershipAllAlphaLeft
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)

theorem simRuleAllFresh_allMembershipBoundDiagonal (e s d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  let q : M := ^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_membershipBoundDiagonal,fixedTranslation_membershipBoundDiagonal]
  · exact targetMembershipAllAlphaDiagonal _ _ (ne_of_lt (lt_add_one _))
  · exact targetMembershipAllAlphaDiagonal _ _ (Ne.symm (ne_of_lt (lt_add_one _)))

theorem simRuleAllFresh_allNegativeMembershipBoundLeft (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]))))) := by
  let q : M := ^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipBoundLeft,fixedTranslation_negativeMembershipBoundLeft]
  · apply targetNegMembershipAllAlphaRight
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetNegMembershipAllAlphaRight
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)

theorem simRuleAllFresh_allNegativeMembershipBoundRight (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))))) := by
  let q : M := ^∀ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipBoundRight,fixedTranslation_negativeMembershipBoundRight]
  · apply targetNegMembershipAllAlphaLeft
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetNegMembershipAllAlphaLeft
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)

theorem simRuleAllFresh_allNegativeMembershipBoundDiagonal (e s d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  let q : M := ^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipBoundDiagonal,fixedTranslation_negativeMembershipBoundDiagonal]
  · exact targetNegMembershipAllAlphaDiagonal _ _ (ne_of_lt (lt_add_one _))
  · exact targetNegMembershipAllAlphaDiagonal _ _ (Ne.symm (ne_of_lt (lt_add_one _)))

theorem targetAllAlpha_of_vacuities (x y A : M)
    (hx : TargetProvable (impValue A (allValue x A)))
    (hy : TargetProvable (impValue A (allValue y A))) :
    TargetProvable (impValue (allValue x A) (allValue y A)) :=
  imp_trans (targetAllSpecialize_of_vacuity x A hx) hy

theorem simRuleAllFresh_allMembershipFree (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^rel (2 : M) (1 : M) ?[^&i,^&j])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^&i,^&j])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) ?[^&i,^&j]))))) := by
  let q : M := ^∀ (^rel (2 : M) (1 : M) ?[^&i,^&j])
  have hxi : simBase e ≠ (simFree e).[i] := ne_of_gt (rankedEnvironment_free_lt e i ha.1)
  have hxj : simBase e ≠ (simFree e).[j] := ne_of_gt (rankedEnvironment_free_lt e j ha.1)
  have hyi : simBase e+1 ≠ (simFree e).[i] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  have hyj : simBase e+1 ≠ (simFree e).[j] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1) (lt_add_one _))
  have hx : TargetProvable (impValue (memValue (simFree e).[j] (simFree e).[i]) (allValue (simBase e) (memValue (simFree e).[j] (simFree e).[i]))) := membershipVacuity_target _ _ _ hxj hxi
  have hy : TargetProvable (impValue (memValue (simFree e).[j] (simFree e).[i]) (allValue (simBase e+1) (memValue (simFree e).[j] (simFree e).[i]))) := membershipVacuity_target _ _ _ hyj hyi
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^&i,^&j]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_membershipFree,fixedTranslation_membershipFree]
  · exact targetAllAlpha_of_vacuities _ _ _ hx hy
  · exact targetAllAlpha_of_vacuities _ _ _ hy hx

theorem simRuleAllFresh_allNegativeMembershipFree (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^nrel (2 : M) (1 : M) ?[^&i,^&j])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^&i,^&j])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) ?[^&i,^&j]))))) := by
  let q : M := ^∀ (^nrel (2 : M) (1 : M) ?[^&i,^&j])
  have hxi : simBase e ≠ (simFree e).[i] := ne_of_gt (rankedEnvironment_free_lt e i ha.1)
  have hxj : simBase e ≠ (simFree e).[j] := ne_of_gt (rankedEnvironment_free_lt e j ha.1)
  have hyi : simBase e+1 ≠ (simFree e).[i] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  have hyj : simBase e+1 ≠ (simFree e).[j] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1) (lt_add_one _))
  have hx : TargetProvable (impValue (negValue (memValue (simFree e).[j] (simFree e).[i])) (allValue (simBase e) (negValue (memValue (simFree e).[j] (simFree e).[i])))) := negationVacuity _ _ (membershipVacuity_target _ _ _ hxj hxi)
  have hy : TargetProvable (impValue (negValue (memValue (simFree e).[j] (simFree e).[i])) (allValue (simBase e+1) (negValue (memValue (simFree e).[j] (simFree e).[i])))) := negationVacuity _ _ (membershipVacuity_target _ _ _ hyj hyi)
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^&i,^&j]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^nrel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_]))
    rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipFree,fixedTranslation_negativeMembershipFree]
  · exact targetAllAlpha_of_vacuities _ _ _ hx hy
  · exact targetAllAlpha_of_vacuities _ _ _ hy hx

/-- The quantified membership-atom eigenlabel field on arbitrary internal vectors. -/
theorem simRuleAllFresh_allMembershipCode (e s v d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^rel (2 : M) (1 : M) v)) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) v)))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∀ (^rel (2 : M) (1 : M) v))))) := by
  have hf := (hs _ hq).isUFormula
  have hv := (IsUFormula.rel.mp (IsUFormula.all.mp hf)).2
  obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
  have hformula : IsFormula SourceL (^∀ (^rel (2 : M) (1 : M) ?[a,b])) := hs _ hq
  have hbody : IsSemiformula SourceL 1 (^rel (2 : M) (1 : M) ?[a,b]) := by
    simpa only [IsSemiformula.all,zero_add] using hformula
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hbody).2
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_allMembershipBoundDiagonal e s d hs hq ha hb
    · exact simRuleAllFresh_allMembershipBoundLeft e s j d hs hq ha hb
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_allMembershipBoundRight e s i d hs hq ha hb
    · exact simRuleAllFresh_allMembershipFree e s i j d hs hq ha hb

/-- The quantified membership-atom eigenlabel field on arbitrary internal vectors. -/
theorem simRuleAllFresh_allNegativeMembershipCode (e s v d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∀ (^nrel (2 : M) (1 : M) v)) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) v)))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∀ (^nrel (2 : M) (1 : M) v))))) := by
  have hf := (hs _ hq).isUFormula
  have hv := (IsUFormula.nrel.mp (IsUFormula.all.mp hf)).2
  obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
  have hformula : IsFormula SourceL (^∀ (^nrel (2 : M) (1 : M) ?[a,b])) := hs _ hq
  have hbody : IsSemiformula SourceL 1 (^nrel (2 : M) (1 : M) ?[a,b]) := by
    simpa only [IsSemiformula.all,zero_add] using hformula
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hbody).2
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_allNegativeMembershipBoundDiagonal e s d hs hq ha hb
    · exact simRuleAllFresh_allNegativeMembershipBoundLeft e s j d hs hq ha hb
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_allNegativeMembershipBoundRight e s i d hs hq ha hb
    · exact simRuleAllFresh_allNegativeMembershipFree e s i j d hs hq ha hb

theorem targetMembershipExAlphaLeft (x y a : M) (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (exValue x ((memValue x a)))
      (exValue y ((memValue y a)))) :=
  contrapose (targetNegMembershipAllAlphaLeft y x a (Ne.symm hxy) hya hxa)

theorem targetMembershipExAlphaRight (x y a : M) (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (exValue x ((memValue a x)))
      (exValue y ((memValue a y)))) :=
  contrapose (targetNegMembershipAllAlphaRight y x a (Ne.symm hxy) hya hxa)

theorem targetMembershipExAlphaDiagonal (x y : M) (hxy : x ≠ y) :
    TargetProvable (impValue (exValue x ((memValue x x)))
      (exValue y ((memValue y y)))) :=
  contrapose (targetNegMembershipAllAlphaDiagonal y x (Ne.symm hxy))

theorem targetNegMembershipExAlphaLeft (x y a : M) (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (exValue x (negValue (memValue x a)))
      (exValue y (negValue (memValue y a)))) :=
  contrapose (imp_trans (liftImp y (doubleNegationElimination (memValue y a)))
    (imp_trans (targetMembershipAllAlphaLeft y x a (Ne.symm hxy) hya hxa)
      (liftImp x (doubleNegationIntroduction (memValue x a)))))

theorem targetNegMembershipExAlphaRight (x y a : M) (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    TargetProvable (impValue (exValue x (negValue (memValue a x)))
      (exValue y (negValue (memValue a y)))) :=
  contrapose (imp_trans (liftImp y (doubleNegationElimination (memValue a y)))
    (imp_trans (targetMembershipAllAlphaRight y x a (Ne.symm hxy) hya hxa)
      (liftImp x (doubleNegationIntroduction (memValue a x)))))

theorem targetNegMembershipExAlphaDiagonal (x y : M) (hxy : x ≠ y) :
    TargetProvable (impValue (exValue x (negValue (memValue x x)))
      (exValue y (negValue (memValue y y)))) :=
  contrapose (imp_trans (liftImp y (doubleNegationElimination (memValue y y)))
    (imp_trans (targetMembershipAllAlphaDiagonal y x (Ne.symm hxy))
      (liftImp x (doubleNegationIntroduction (memValue x x)))))

theorem simRuleAllFresh_exMembershipBoundLeft (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]))))) := by
  let q : M := ^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_membershipBoundLeft,fixedTranslation_membershipBoundLeft]
  · apply targetMembershipExAlphaRight
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetMembershipExAlphaRight
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)

theorem simRuleAllFresh_exMembershipBoundRight (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))))) := by
  let q : M := ^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_membershipBoundRight,fixedTranslation_membershipBoundRight]
  · apply targetMembershipExAlphaLeft
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetMembershipExAlphaLeft
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)

theorem simRuleAllFresh_exMembershipBoundDiagonal (e s d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  let q : M := ^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_membershipBoundDiagonal,fixedTranslation_membershipBoundDiagonal]
  · exact targetMembershipExAlphaDiagonal _ _ (ne_of_lt (lt_add_one _))
  · exact targetMembershipExAlphaDiagonal _ _ (Ne.symm (ne_of_lt (lt_add_one _)))

theorem simRuleAllFresh_exMembershipFree (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^rel (2 : M) (1 : M) ?[^&i,^&j])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^&i,^&j])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^&i,^&j]))))) := by
  let q : M := ^∃ (^rel (2 : M) (1 : M) ?[^&i,^&j])
  have hxi : simBase e ≠ (simFree e).[i] := ne_of_gt (rankedEnvironment_free_lt e i ha.1)
  have hxj : simBase e ≠ (simFree e).[j] := ne_of_gt (rankedEnvironment_free_lt e j ha.1)
  have hyi : simBase e+1 ≠ (simFree e).[i] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  have hyj : simBase e+1 ≠ (simFree e).[j] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1) (lt_add_one _))
  have hx : TargetProvable (impValue (memValue (simFree e).[j] (simFree e).[i]) (allValue (simBase e) (memValue (simFree e).[j] (simFree e).[i]))) := membershipVacuity_target _ _ _ hxj hxi
  have hy : TargetProvable (impValue (memValue (simFree e).[j] (simFree e).[i]) (allValue (simBase e+1) (memValue (simFree e).[j] (simFree e).[i]))) := membershipVacuity_target _ _ _ hyj hyi
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp
    have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^&i,^&j]) := by
      simpa only [IsUFormula.rel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_membershipFree,fixedTranslation_membershipFree]
  · exact contrapose (targetAllAlpha_of_vacuities _ _ _ (negationVacuity _ _ hy) (negationVacuity _ _ hx))
  · exact contrapose (targetAllAlpha_of_vacuities _ _ _ (negationVacuity _ _ hx) (negationVacuity _ _ hy))

theorem simRuleAllFresh_exNegativeMembershipBoundLeft (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]))))) := by
  let q : M := ^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipBoundLeft,fixedTranslation_negativeMembershipBoundLeft]
  · apply targetNegMembershipExAlphaRight
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetNegMembershipExAlphaRight
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)

theorem simRuleAllFresh_exNegativeMembershipBoundRight (e s i d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))))) := by
  let q : M := ^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipBoundRight,fixedTranslation_negativeMembershipBoundRight]
  · apply targetNegMembershipExAlphaLeft
    · exact ne_of_lt (lt_add_one _)
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  · apply targetNegMembershipExAlphaLeft
    · exact Ne.symm (ne_of_lt (lt_add_one _))
    · exact ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
    · exact ne_of_gt (rankedEnvironment_free_lt e i ha.1)

theorem simRuleAllFresh_exNegativeMembershipBoundDiagonal (e s d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  let q : M := ^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipBoundDiagonal,fixedTranslation_negativeMembershipBoundDiagonal]
  · exact targetNegMembershipExAlphaDiagonal _ _ (ne_of_lt (lt_add_one _))
  · exact targetNegMembershipExAlphaDiagonal _ _ (Ne.symm (ne_of_lt (lt_add_one _)))

theorem simRuleAllFresh_exNegativeMembershipFree (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^&j])) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^&j])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^&j]))))) := by
  let q : M := ^∃ (^nrel (2 : M) (1 : M) ?[^&i,^&j])
  have hxi : simBase e ≠ (simFree e).[i] := ne_of_gt (rankedEnvironment_free_lt e i ha.1)
  have hxj : simBase e ≠ (simFree e).[j] := ne_of_gt (rankedEnvironment_free_lt e j ha.1)
  have hyi : simBase e+1 ≠ (simFree e).[i] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e i ha.1) (lt_add_one _))
  have hyj : simBase e+1 ≠ (simFree e).[j] := ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1) (lt_add_one _))
  have hx : TargetProvable (impValue (negValue (memValue (simFree e).[j] (simFree e).[i])) (allValue (simBase e) (negValue (memValue (simFree e).[j] (simFree e).[i])))) := negationVacuity _ _ (membershipVacuity_target _ _ _ hxj hxi)
  have hy : TargetProvable (impValue (negValue (memValue (simFree e).[j] (simFree e).[i])) (allValue (simBase e+1) (negValue (memValue (simFree e).[j] (simFree e).[i])))) := negationVacuity _ _ (membershipVacuity_target _ _ _ hyj hyi)
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
    have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp
    have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^&i,^&j]) := by
      simpa only [IsUFormula.nrel] using And.intro hr hv
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_])
      (F fixedFormulaTranslation ![^∃ (^nrel (2 : M) (1 : M) ?[^&i,^&j]),_,_,_,_]))
    rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp,
      fixedTranslation_negativeMembershipFree,fixedTranslation_negativeMembershipFree]
  · exact contrapose (targetAllAlpha_of_vacuities _ _ _ (negationVacuity _ _ hy) (negationVacuity _ _ hx))
  · exact contrapose (targetAllAlpha_of_vacuities _ _ _ (negationVacuity _ _ hx) (negationVacuity _ _ hy))

/-- The existential-membership eigenlabel field on arbitrary internal vectors. -/
theorem simRuleAllFresh_exMembershipCode (e s v d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^rel (2 : M) (1 : M) v)) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) v)))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) v))))) := by
  have hf := (hs _ hq).isUFormula
  have hv := (IsUFormula.rel.mp (IsUFormula.ex.mp hf)).2
  obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
  have hformula : IsFormula SourceL (^∃ (^rel (2 : M) (1 : M) ?[a,b])) := hs _ hq
  have hbody : IsSemiformula SourceL 1 (^rel (2 : M) (1 : M) ?[a,b]) := by
    simpa only [IsSemiformula.exs,zero_add] using hformula
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hbody).2
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_exMembershipBoundDiagonal e s d hs hq ha hb
    · exact simRuleAllFresh_exMembershipBoundLeft e s j d hs hq ha hb
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_exMembershipBoundRight e s i d hs hq ha hb
    · exact simRuleAllFresh_exMembershipFree e s i j d hs hq ha hb

/-- The existential-membership eigenlabel field on arbitrary internal vectors. -/
theorem simRuleAllFresh_exNegativeMembershipCode (e s v d : M)
    (hs : IsFormulaSet SourceL s) (hq : (^∃ (^nrel (2 : M) (1 : M) v)) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) v)))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) v))))) := by
  have hf := (hs _ hq).isUFormula
  have hv := (IsUFormula.nrel.mp (IsUFormula.ex.mp hf)).2
  obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
  have hformula : IsFormula SourceL (^∃ (^nrel (2 : M) (1 : M) ?[a,b])) := hs _ hq
  have hbody : IsSemiformula SourceL 1 (^nrel (2 : M) (1 : M) ?[a,b]) := by
    simpa only [IsSemiformula.exs,zero_add] using hformula
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hbody).2
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_exNegativeMembershipBoundDiagonal e s d hs hq ha hb
    · exact simRuleAllFresh_exNegativeMembershipBoundLeft e s j d hs hq ha hb
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleAllFresh_exNegativeMembershipBoundRight e s i d hs hq ha hb
    · exact simRuleAllFresh_exNegativeMembershipFree e s i j d hs hq ha hb

#print axioms targetMembershipAllAlphaRight
#print axioms targetMembershipAllAlphaLeft
#print axioms targetMembershipAllAlphaDiagonal
#print axioms targetNegMembershipAllAlphaRight
#print axioms targetNegMembershipAllAlphaLeft
#print axioms targetNegMembershipAllAlphaDiagonal
#print axioms simRuleAllFresh_allMembershipBoundLeft
#print axioms simRuleAllFresh_allMembershipCode
#print axioms simRuleAllFresh_allNegativeMembershipCode
#print axioms simRuleAllFresh_exMembershipCode
#print axioms simRuleAllFresh_exNegativeMembershipCode
end models
end PA194ModelLogic
