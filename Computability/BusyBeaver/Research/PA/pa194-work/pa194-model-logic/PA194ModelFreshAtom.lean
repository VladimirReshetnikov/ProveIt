import PA194ModelSourceShiftAtom
import PA194ModelSourceIndexBound
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
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
local instance freshAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freshAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freshAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freshAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freshAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance freshAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem iffVacuity_target (x a b : M)
    (ha : TargetProvable (impValue a (allValue x a)))
    (hb : TargetProvable (impValue b (allValue x b))) :
    TargetProvable (impValue (iffValue a b) (allValue x (iffValue a b))) := by
  unfold iffValue
  exact conjunctionVacuity x _ _ (implicationVacuity x a b ha hb) (implicationVacuity x b a hb ha)

theorem neighborhoodVacuity_target (x a b z : M) (hxa : x ≠ a) (hxb : x ≠ b) (hxz : x ≠ z) :
    TargetProvable (impValue (neighborhoodValue a b z) (allValue x (neighborhoodValue a b z))) := by
  unfold neighborhoodValue
  apply conjunctionVacuity
  · apply universalVacuity
    exact iffVacuity_target x _ _ (membershipVacuity_target a z x hxa hxz)
      (membershipVacuity_target b z x hxb hxz)
  · apply universalVacuity
    exact iffVacuity_target x _ _ (membershipVacuity_target z a x hxz hxa)
      (membershipVacuity_target z b x hxz hxb)

theorem positiveAtomVacuity (e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (hxa : simBase e ≠ F termLabelCode ![a,simBound e,simFree e])
    (hxb : simBase e ≠ F termLabelCode ![b,simBound e,simFree e])
    (hxz : simBase e ≠ simReserve e) :
    let A := F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],simBound e,simFree e,simBase e,simReserve e]
    TargetProvable (impValue A (allValue (simBase e) A)) := by
  dsimp only
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have hr' : r = 0 ∨ r = 1 := by
    have h := hr
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at h
    simpa using h
  rw [fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv]
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model]
    exact neighborhoodVacuity_target _ _ _ _ hxa hxb hxz
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model]
    exact membershipVacuity_target _ _ _ hxb hxa

theorem simRuleAllFresh_positiveAtom (e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (hxa : simBase e ≠ F termLabelCode ![a,simBound e,simFree e])
    (hxb : simBase e ≠ F termLabelCode ![b,simBound e,simFree e])
    (hxz : simBase e ≠ simReserve e) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^rel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^rel (2 : M) r ?[a,b])))) := by
  change TargetProvable (impValue (negatedTranslation e (^rel (2 : M) r ?[a,b]))
    (allValue (simBase e) (negatedTranslation e (^rel (2 : M) r ?[a,b]))))
  rw [negatedTranslation_any]
  exact negationVacuity _ _ (positiveAtomVacuity e r a b hr ha hb hxa hxb hxz)

theorem simRuleAllFresh_negativeAtom (e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (hxa : simBase e ≠ F termLabelCode ![a,simBound e,simFree e])
    (hxb : simBase e ≠ F termLabelCode ![b,simBound e,simFree e])
    (hxz : simBase e ≠ simReserve e) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b])))) := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  change TargetProvable (impValue (negatedTranslation e (^nrel (2 : M) r ?[a,b]))
    (allValue (simBase e) (negatedTranslation e (^nrel (2 : M) r ?[a,b]))))
  rw [negatedTranslation_any,fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact negationVacuity _ _ (negationVacuity _ _ (positiveAtomVacuity e r a b hr ha hb hxa hxb hxz))

/-- A closed source term uses only a free-stack entry below any enclosing
formula bound; the bound applies to nonstandard model indices as well. -/
theorem closedTerm_label_lt (t bound freeEnv base q s : M)
    (ht : IsSemiterm SourceL 0 t) (htq : t < q) (hqs : q < s)
    (hstack : ∀ i < s, freeEnv.[i] < base) :
    F termLabelCode ![t,bound,freeEnv] < base := by
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨i,hi⟩ | ⟨i,hi⟩
  · subst t
    have h : i < (0 : M) := by simpa only [IsSemiterm.bvar] using ht
    exact False.elim (not_lt_zero h)
  · subst t
    rw [termLabel_free_nth]
    apply hstack i
    exact lt_trans (freeVariable_index_lt i) (lt_trans htq hqs)

theorem simRuleAllFresh_closedPositiveAtom (e s r a b : M)
    (hs : IsFormulaSet SourceL s) (hq : (^rel (2 : M) r ?[a,b]) ∈ s)
    (hstack : ∀ i < s, (simFree e).[i] < simBase e)
    (hxz : simBase e ≠ simReserve e) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^rel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^rel (2 : M) r ?[a,b])))) := by
  have hformula := hs _ hq
  have hparts := IsSemiformula.rel.mp hformula
  have hr := hparts.1
  have ht : IsSemitermVec SourceL 2 0 (?[a,b] : M) := hparts.2
  obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp ht
  have hq_lt : (^rel (2 : M) r ?[a,b]) < s := lt_of_mem hq
  have hvlt := vector_lt_atom 0 r (pair a (pair b 0+1)+1)
  have ha' : a < (^rel (2 : M) r ?[a,b]) := by
    exact lt_trans (pairVector_term_lt a b).1 (by simpa only [qqRel,adjoin_def] using hvlt)
  have hb' : b < (^rel (2 : M) r ?[a,b]) := by
    exact lt_trans (pairVector_term_lt a b).2 (by simpa only [qqRel,adjoin_def] using hvlt)
  have hla := closedTerm_label_lt a (simBound e) (simFree e) (simBase e) _ s ha ha' hq_lt hstack
  have hlb := closedTerm_label_lt b (simBound e) (simFree e) (simBase e) _ s hb hb' hq_lt hstack
  exact simRuleAllFresh_positiveAtom e r a b hr ha.isUTerm hb.isUTerm (ne_of_gt hla) (ne_of_gt hlb) hxz

theorem simRuleAllFresh_closedNegativeAtom (e s r a b : M)
    (hs : IsFormulaSet SourceL s) (hq : (^nrel (2 : M) r ?[a,b]) ∈ s)
    (hstack : ∀ i < s, (simFree e).[i] < simBase e)
    (hxz : simBase e ≠ simReserve e) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b])))) := by
  have hformula := hs _ hq
  have hparts := IsSemiformula.nrel.mp hformula
  have hr := hparts.1
  have ht : IsSemitermVec SourceL 2 0 (?[a,b] : M) := hparts.2
  obtain ⟨ha,hb⟩ := IsSemitermVec.doubleton.mp ht
  have hq_lt : (^nrel (2 : M) r ?[a,b]) < s := lt_of_mem hq
  have hvlt := vector_lt_atom 1 r (pair a (pair b 0+1)+1)
  have ha' : a < (^nrel (2 : M) r ?[a,b]) := by
    exact lt_trans (pairVector_term_lt a b).1 (by simpa only [qqNRel,adjoin_def] using hvlt)
  have hb' : b < (^nrel (2 : M) r ?[a,b]) := by
    exact lt_trans (pairVector_term_lt a b).2 (by simpa only [qqNRel,adjoin_def] using hvlt)
  have hla := closedTerm_label_lt a (simBound e) (simFree e) (simBase e) _ s ha ha' hq_lt hstack
  have hlb := closedTerm_label_lt b (simBound e) (simFree e) (simBase e) _ s hb hb' hq_lt hstack
  exact simRuleAllFresh_negativeAtom e r a b hr ha.isUTerm hb.isUTerm (ne_of_gt hla) (ne_of_gt hlb) hxz

#print axioms closedTerm_label_lt
#print axioms simRuleAllFresh_closedPositiveAtom
#print axioms simRuleAllFresh_closedNegativeAtom
#print axioms neighborhoodVacuity_target
#print axioms positiveAtomVacuity
#print axioms simRuleAllFresh_positiveAtom
#print axioms simRuleAllFresh_negativeAtom
end models
end PA194ModelLogic
