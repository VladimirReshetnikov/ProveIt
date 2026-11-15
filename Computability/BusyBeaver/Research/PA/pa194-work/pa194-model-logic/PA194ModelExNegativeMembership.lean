import PA194ModelExMembership
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
local instance exNegZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exNegOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exNegAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exNegMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exNegLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exNegIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]



/-- Contrapose a target specialization to introduce an existential negation. -/
theorem targetExistsNeg_of_specialize (x P Q : M)
    (hs : TargetProvable (impValue (allValue x P) Q)) :
    TargetProvable (impValue (negValue Q) (exValue x (negValue P))) := by
  have hh : TargetProvable (impValue (allValue x (negValue (negValue P))) Q) :=
    imp_trans (liftImp x (doubleNegationElimination P)) hs
  let hn : Ctx [allValue x (negValue (negValue P)),negValue Q] (negValue Q) := .assumption (by simp)
  let hu : Ctx [allValue x (negValue (negValue P)),negValue Q] (allValue x (negValue (negValue P))) := .assumption (by simp)
  exact (Ctx.mp (.mp hu (.closed hh)) hn).deduction.deduction.empty

theorem targetExistsNegMembershipLeft (x c a : M) (hxc : x ≠ c) (hxa : x ≠ a) :
    TargetProvable (impValue (negValue (memValue c a)) (exValue x (negValue (memValue x a)))) := by
  apply targetExistsNeg_of_specialize
  exact specializeWithMirroredEquality_target x c _ _
    (membershipVacuity_target c a x hxc hxa) (reverseLeft_target c x a)

theorem targetExistsNegMembershipRight (x c a : M) (hxc : x ≠ c) (hxa : x ≠ a) :
    TargetProvable (impValue (negValue (memValue a c)) (exValue x (negValue (memValue a x)))) := by
  apply targetExistsNeg_of_specialize
  exact specializeWithMirroredEquality_target x c _ _
    (membershipVacuity_target a c x hxa hxc) (reverseRight_target c x a)

theorem targetExistsNegMembershipDiagonal (x c : M) (hxc : x ≠ c) :
    TargetProvable (impValue (negValue (memValue c c)) (exValue x (negValue (memValue x x)))) := by
  apply targetExistsNeg_of_specialize
  apply specializeWithMirroredEquality_target x c _ _ (membershipVacuity_target c c x hxc hxc)
  let he : Ctx [memValue x x,eqValue c x] (eqValue c x) := .assumption (by simp)
  let hm : Ctx [memValue x x,eqValue c x] (memValue x x) := .assumption (by simp)
  let h1 : Ctx [memValue x x,eqValue c x] (memValue c x) := .mp hm (.mp he (.closed (reverseLeft_target c x x)))
  let h2 : Ctx [memValue x x,eqValue c x] (memValue c c) := .mp h1 (.mp he (.closed (reverseRight_target c x c)))
  exact h2.deduction.deduction.empty
theorem substs1_negativeMembershipBoundLeft (i j : M) :
    substs1 SourceL (^&j) (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]) =
      ^nrel (2 : M) (1 : M) ?[^&j,^&i] := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hb : IsUTerm SourceL (^&i) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp [ha,hb]
  rw [substs1,substs_nrel hr hv,termSubstVec_cons₂ ha hb]
  simp


theorem fixedTranslation_negativeMembershipBoundLeft (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i],
      pair base bound+1,free,base+1,reserve] = negValue (memValue (free.[i]) base) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedTranslation_membershipBoundLeft]

theorem fixedTranslation_negativeMembershipFree (i j bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (1 : M) ?[^&j,^&i],bound,free,base,reserve] =
      negValue (memValue (free.[i]) (free.[j])) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^&j,^&i] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedTranslation_membershipFree]

theorem simRuleExs_negativeMembershipBoundLeft (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [substs1_negativeMembershipBoundLeft i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_negativeMembershipBoundLeft,fixedTranslation_negativeMembershipFree]
  exact targetExistsNegMembershipRight _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))

theorem substs1_negativeMembershipBoundRight (i j : M) :
    substs1 SourceL (^&j) (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) =
      ^nrel (2 : M) (1 : M) ?[^&i,^&j] := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have ha : IsUTerm SourceL (^&i) := by simp
  have hb : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp [ha,hb]
  rw [substs1,substs_nrel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem fixedTranslation_negativeMembershipBoundRight (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = negValue (memValue base (free.[i])) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedTranslation_membershipBoundRight]

theorem simRuleExs_negativeMembershipBoundRight (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [substs1_negativeMembershipBoundRight i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_negativeMembershipBoundRight,fixedTranslation_negativeMembershipFree]
  exact targetExistsNegMembershipLeft _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))

theorem substs1_negativeMembershipBoundDiagonal (j : M) :
    substs1 SourceL (^&j) (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) =
      ^nrel (2 : M) (1 : M) ?[^&j,^&j] := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp [ha]
  rw [substs1,substs_nrel hr hv,termSubstVec_cons₂ ha ha]
  simp

theorem fixedTranslation_negativeMembershipBoundDiagonal (bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = negValue (memValue base base) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedTranslation_membershipBoundDiagonal]

theorem simRuleExs_negativeMembershipBoundDiagonal (e s j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [substs1_negativeMembershipBoundDiagonal j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_negativeMembershipBoundDiagonal,fixedTranslation_negativeMembershipFree]
  exact targetExistsNegMembershipDiagonal _ _ (ne_of_gt (rankedEnvironment_free_lt e j ha.1))

theorem simRuleExs_negativeMembershipBoundDiagonal_term (e s t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_negativeMembershipBoundDiagonal e s j d hs hm ha

theorem simRuleExs_negativeMembershipBoundLeft_term (e s i t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^#(0 : M),^&i]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_negativeMembershipBoundLeft e s i j d hs hm ha

theorem simRuleExs_negativeMembershipBoundRight_term (e s i t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[^&i,^#(0 : M)]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_negativeMembershipBoundRight e s i j d hs hm ha

theorem simRuleExs_negativeMembershipAtom (e s a b t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) ?[a,b])) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel (2 : M) (1 : M) ?[a,b]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) ?[a,b]))) 1)) := by
  have hf : IsFormula SourceL (^∃ (^nrel (2 : M) (1 : M) ?[a,b])) := hs _ hm
  have hbody : IsSemiformula SourceL 1 (^nrel (2 : M) (1 : M) ?[a,b]) := by
    simpa only [IsSemiformula.exs,zero_add] using hf
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hbody).2
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleExs_negativeMembershipBoundDiagonal_term e s t d hs hm ht ha
    · exact simRuleExs_negativeMembershipBoundLeft_term e s j t d hs hm ht ha
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨j,rfl⟩)
    · exact simRuleExs_negativeMembershipBoundRight_term e s i t d hs hm ht ha
    · exact simRuleExs_negativeFvars e s (1 : M) i j t d hs hm ht relExt_relation_one ha

#print axioms targetExistsNeg_of_specialize
#print axioms targetExistsNegMembershipLeft
#print axioms targetExistsNegMembershipRight
#print axioms targetExistsNegMembershipDiagonal
#print axioms simRuleExs_negativeMembershipBoundLeft
#print axioms simRuleExs_negativeMembershipBoundRight
#print axioms simRuleExs_negativeMembershipBoundDiagonal_term
#print axioms simRuleExs_negativeMembershipAtom
end models
end PA194ModelLogic
