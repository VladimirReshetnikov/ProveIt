import PA194ModelExBridge
import PA194ModelFreshBoolean
import PA194ModelRankedEnvironment
import PA194ModelUniversalSpecialization
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
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
local instance exMemberZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exMemberOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exMemberAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exMemberMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exMemberLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exMemberIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-- A genuine target substitution at the first membership argument. -/
theorem targetExistsMembershipLeft (x c a : M) (hxc : x ≠ c) (hxa : x ≠ a) :
    TargetProvable (impValue (memValue c a) (exValue x (memValue x a))) := by
  let P := memValue x a
  let Q := memValue c a
  have hv : TargetProvable (impValue (negValue Q) (allValue x (negValue Q))) :=
    negationVacuity x Q (membershipVacuity_target c a x hxc hxa)
  have hr : TargetProvable (impValue (eqValue c x) (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,eqValue c x] (eqValue c x) := .assumption (by simp)
    let hp : Ctx [Q,negValue P,eqValue c x] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,eqValue c x] Q := .assumption (by simp)
    let hp' : Ctx [Q,negValue P,eqValue c x] P := .mp hq (.mp he (.closed (memLeft c x a)))
    exact (Ctx.mp hp' hp).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x c (negValue P) (negValue Q) hv hr
  let hq : Ctx [allValue x (negValue P),Q] Q := .assumption (by simp)
  let hall : Ctx [allValue x (negValue P),Q] (allValue x (negValue P)) := .assumption (by simp)
  let hn : Ctx [allValue x (negValue P),Q] (negValue Q) := .mp hall (.closed hs)
  exact (Ctx.mp hq hn).deduction.deduction.empty

/-- The source membership decoder reverses the two numeric arguments. -/
theorem targetExistsMembershipRight (x c a : M) (hxc : x ≠ c) (hxa : x ≠ a) :
    TargetProvable (impValue (memValue a c) (exValue x (memValue a x))) := by
  let P := memValue a x
  let Q := memValue a c
  have hv : TargetProvable (impValue (negValue Q) (allValue x (negValue Q))) :=
    negationVacuity x Q (membershipVacuity_target a c x hxa hxc)
  have hr : TargetProvable (impValue (eqValue c x) (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,eqValue c x] (eqValue c x) := .assumption (by simp)
    let hp : Ctx [Q,negValue P,eqValue c x] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,eqValue c x] Q := .assumption (by simp)
    let hp' : Ctx [Q,negValue P,eqValue c x] P := .mp hq (.mp he (.closed (memRight c x a)))
    exact (Ctx.mp hp' hp).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x c (negValue P) (negValue Q) hv hr
  let hq : Ctx [allValue x (negValue P),Q] Q := .assumption (by simp)
  let hall : Ctx [allValue x (negValue P),Q] (allValue x (negValue P)) := .assumption (by simp)
  let hn : Ctx [allValue x (negValue P),Q] (negValue Q) := .mp hall (.closed hs)
  exact (Ctx.mp hq hn).deduction.deduction.empty

theorem substs1_membershipBoundLeft (i j : M) :
    substs1 SourceL (^&j) (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]) =
      ^rel (2 : M) (1 : M) ?[^&j,^&i] := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hb : IsUTerm SourceL (^&i) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp [ha,hb]
  rw [substs1,substs_rel hr hv,termSubstVec_cons₂ ha hb]
  simp


theorem fixedTranslation_membershipBoundLeft (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (1 : M) ?[^#(0 : M),^&i],
      pair base bound+1,free,base+1,reserve] = memValue (free.[i]) base := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
  rw [membershipAtom_model,termLabel_bound_nth,termLabel_free_nth]
  rw [←adjoin_def,nth_adjoin_zero]

theorem fixedTranslation_membershipFree (i j bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (1 : M) ?[^&j,^&i],bound,free,base,reserve] =
      memValue (free.[i]) (free.[j]) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^&j,^&i] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
  rw [membershipAtom_model,termLabel_free_nth,termLabel_free_nth]


/-- The exact source existential field with a genuinely substituted bound variable. -/
theorem simRuleExs_membershipBoundLeft (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [substs1_membershipBoundLeft i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_membershipBoundLeft,fixedTranslation_membershipFree]
  exact targetExistsMembershipRight _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))

theorem substs1_membershipBoundRight (i j : M) :
    substs1 SourceL (^&j) (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) =
      ^rel (2 : M) (1 : M) ?[^&i,^&j] := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have ha : IsUTerm SourceL (^&i) := by simp
  have hb : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp [ha,hb]
  rw [substs1,substs_rel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem fixedTranslation_membershipBoundRight (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = memValue base (free.[i]) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
  rw [membershipAtom_model,termLabel_free_nth,termLabel_bound_nth]
  rw [←adjoin_def,nth_adjoin_zero]

theorem simRuleExs_membershipBoundRight (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [substs1_membershipBoundRight i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_membershipBoundRight,fixedTranslation_membershipFree]
  exact targetExistsMembershipLeft _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))

/-- The function-free source language has only free variables as closed terms. -/
theorem sourceClosedTerm_is_fvar (t : M) (ht : IsTerm SourceL t) : ∃ j : M, t = ^&j := by
  change IsSemiterm SourceL 0 t at ht
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨i,hi⟩ | ⟨i,hi⟩
  · subst t
    have h : i < (0 : M) := by simpa only [IsSemiterm.bvar] using ht
    exact False.elim (not_lt_zero h)
  · exact ⟨i,hi⟩

theorem simRuleExs_membershipBoundLeft_term (e s i t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_membershipBoundLeft e s i j d hs hm ha

theorem simRuleExs_membershipBoundRight_term (e s i t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_membershipBoundRight e s i j d hs hm ha

theorem targetExistsMembershipDiagonal (x c : M) (hxc : x ≠ c) :
    TargetProvable (impValue (memValue c c) (exValue x (memValue x x))) := by
  let P := memValue x x
  let Q := memValue c c
  have hv : TargetProvable (impValue (negValue Q) (allValue x (negValue Q))) :=
    negationVacuity x Q (membershipVacuity_target c c x hxc hxc)
  have hr : TargetProvable (impValue (eqValue c x) (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,eqValue c x] (eqValue c x) := .assumption (by simp)
    let hp : Ctx [Q,negValue P,eqValue c x] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,eqValue c x] Q := .assumption (by simp)
    let h1 : Ctx [Q,negValue P,eqValue c x] (memValue x c) := .mp hq (.mp he (.closed (memLeft c x c)))
    let h2 : Ctx [Q,negValue P,eqValue c x] P := .mp h1 (.mp he (.closed (memRight c x x)))
    exact (Ctx.mp h2 hp).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x c (negValue P) (negValue Q) hv hr
  let hq : Ctx [allValue x (negValue P),Q] Q := .assumption (by simp)
  let hall : Ctx [allValue x (negValue P),Q] (allValue x (negValue P)) := .assumption (by simp)
  let hn : Ctx [allValue x (negValue P),Q] (negValue Q) := .mp hall (.closed hs)
  exact (Ctx.mp hq hn).deduction.deduction.empty

theorem substs1_membershipBoundDiagonal (j : M) :
    substs1 SourceL (^&j) (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) =
      ^rel (2 : M) (1 : M) ?[^&j,^&j] := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp [ha]
  rw [substs1,substs_rel hr hv,termSubstVec_cons₂ ha ha]
  simp

theorem fixedTranslation_membershipBoundDiagonal (bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = memValue base base := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
  rw [membershipAtom_model,termLabel_bound_nth]
  rw [←adjoin_def,nth_adjoin_zero]

theorem simRuleExs_membershipBoundDiagonal (e s j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [substs1_membershipBoundDiagonal j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_membershipBoundDiagonal,fixedTranslation_membershipFree]
  exact targetExistsMembershipDiagonal _ _ (ne_of_gt (rankedEnvironment_free_lt e j ha.1))

theorem simRuleExs_membershipBoundDiagonal_term (e s t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_membershipBoundDiagonal e s j d hs hm ha

theorem sourceSemitermOne_cases (t : M) (ht : IsSemiterm SourceL 1 t) :
    t = ^#(0 : M) ∨ ∃ i : M, t = ^&i := by
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨i,hi⟩ | ⟨i,hi⟩
  · subst t
    have h : i < (1 : M) := by simpa only [IsSemiterm.bvar] using ht
    have hi0 : i = 0 := by simpa using h
    simp [hi0]
  · exact Or.inr ⟨i,hi⟩

/-- Every well-scoped positive membership atom is handled by the exact
existential compiler implication, for every legal source term. -/
theorem simRuleExs_positiveMembershipAtom (e s a b t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) ?[a,b])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) (1 : M) ?[a,b]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) ?[a,b]))) 1)) := by
  have hf : IsFormula SourceL (^∃ (^rel (2 : M) (1 : M) ?[a,b])) := hs _ hm
  have hbody : IsSemiformula SourceL 1 (^rel (2 : M) (1 : M) ?[a,b]) := by
    simpa only [IsSemiformula.exs,zero_add] using hf
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hbody).2
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleExs_membershipBoundDiagonal_term e s t d hs hm ht ha
    · exact simRuleExs_membershipBoundLeft_term e s j t d hs hm ht ha
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleExs_membershipBoundRight_term e s i t d hs hm ht ha
    · exact simRuleExs_positiveFvars e s (1 : M) i j t d hs hm ht relExt_relation_one ha

/-- The same result directly over an arbitrary internally valid vector code. -/
theorem simRuleExs_positiveMembershipCode (e s v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) (1 : M) v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hv := (IsUFormula.rel.mp (IsUFormula.ex.mp hf)).2
  obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
  exact simRuleExs_positiveMembershipAtom e s a b t d hs hm ht ha

#print axioms targetExistsMembershipLeft
#print axioms targetExistsMembershipRight
#print axioms substs1_membershipBoundLeft
#print axioms fixedTranslation_membershipBoundLeft
#print axioms fixedTranslation_membershipFree
#print axioms simRuleExs_membershipBoundLeft
#print axioms substs1_membershipBoundRight
#print axioms fixedTranslation_membershipBoundRight
#print axioms simRuleExs_membershipBoundRight
#print axioms sourceClosedTerm_is_fvar
#print axioms simRuleExs_membershipBoundLeft_term
#print axioms simRuleExs_membershipBoundRight_term
#print axioms targetExistsMembershipDiagonal
#print axioms substs1_membershipBoundDiagonal
#print axioms fixedTranslation_membershipBoundDiagonal
#print axioms simRuleExs_membershipBoundDiagonal
#print axioms simRuleExs_membershipBoundDiagonal_term
#print axioms sourceSemitermOne_cases
#print axioms simRuleExs_positiveMembershipAtom
#print axioms simRuleExs_positiveMembershipCode
end models
end PA194ModelLogic
