import PA194ModelFullQF
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
local instance alignedAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance alignedAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance alignedAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance alignedAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance alignedAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance alignedAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






def LabelAligned (x y a b : M) : Prop := a = b ∨ (a = x ∧ b = y)

theorem targetPremiseRewrite_trans (E A B C : M)
    (hab : TargetPremiseRewrite E A B) (hbc : TargetPremiseRewrite E B C) :
    TargetPremiseRewrite E A C := by
  constructor
  · let he : Ctx [A,E] E := .assumption (by simp)
    let ha : Ctx [A,E] A := .assumption (by simp)
    let hb : Ctx [A,E] B := .mp ha (.mp he (.closed hab.1))
    exact (Ctx.mp hb (.mp he (.closed hbc.1))).deduction.deduction.empty
  · let he : Ctx [C,E] E := .assumption (by simp)
    let hc : Ctx [C,E] C := .assumption (by simp)
    let hb : Ctx [C,E] B := .mp hc (.mp he (.closed hbc.2))
    exact (Ctx.mp hb (.mp he (.closed hab.2))).deduction.deduction.empty

theorem alignedMembershipFirst (x y a b : M) (h : LabelAligned x y a b) (c : M) :
    TargetPremiseRewrite (eqValue y x) (memValue a c) (memValue b c) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    exact ⟨reverseLeft_target y x c,memLeft y x c⟩

theorem alignedMembershipSecond (x y a b : M) (h : LabelAligned x y a b) (c : M) :
    TargetPremiseRewrite (eqValue y x) (memValue c a) (memValue c b) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    exact ⟨reverseRight_target y x c,memRight y x c⟩

theorem alignedMembership (x y a b c d : M) (ha : LabelAligned x y a b)
    (hc : LabelAligned x y c d) :
    TargetPremiseRewrite (eqValue y x) (memValue a c) (memValue b d) :=
  targetPremiseRewrite_trans _ _ _ _ (alignedMembershipFirst x y a b ha c)
    (alignedMembershipSecond x y c d hc b)

theorem alignedNeighborhoodFirst (x y a b : M) (h : LabelAligned x y a b) (c z : M)
    (hzy : z ≠ y) (hzx : z ≠ x) :
    TargetPremiseRewrite (eqValue y x) (neighborhoodValue a c z) (neighborhoodValue b c z) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    exact equalityNeighborhoodLeftRewrite x y c z hzy hzx

theorem alignedNeighborhoodSecond (x y a b : M) (h : LabelAligned x y a b) (c z : M)
    (hzy : z ≠ y) (hzx : z ≠ x) :
    TargetPremiseRewrite (eqValue y x) (neighborhoodValue c a z) (neighborhoodValue c b z) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    exact equalityNeighborhoodRightRewrite x y c z hzy hzx

theorem alignedNeighborhood (x y a b c d z : M) (ha : LabelAligned x y a b)
    (hc : LabelAligned x y c d) (hzy : z ≠ y) (hzx : z ≠ x) :
    TargetPremiseRewrite (eqValue y x) (neighborhoodValue a c z) (neighborhoodValue b d z) :=
  targetPremiseRewrite_trans _ _ _ _ (alignedNeighborhoodFirst x y a b ha c z hzy hzx)
    (alignedNeighborhoodSecond x y c d hc b z hzy hzx)

theorem alignedTermLabels (x y t bound₁ bound₂ free : M)
    (ht : IsUTerm SourceL t)
    (hbound : ∀ i : M, LabelAligned x y bound₁.[i] bound₂.[i]) :
    LabelAligned x y (F termLabelCode ![t,bound₁,free]) (F termLabelCode ![t,bound₂,free]) := by
  rcases PA194TermShiftModel.term_cases ht with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [termLabel_bound_nth,termLabel_bound_nth]
    exact hbound i
  · rw [termLabel_free_nth,termLabel_free_nth]
    exact Or.inl rfl

theorem alignedPositiveAtom (x y r a b bound₁ bound₂ free base₁ base₂ reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (hbound : ∀ i : M, LabelAligned x y bound₁.[i] bound₂.[i])
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],bound₁,free,base₁,reserve])
      (F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],bound₂,free,base₂,reserve]) := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have ha' := alignedTermLabels x y a bound₁ bound₂ free ha hbound
  have hb' := alignedTermLabels x y b bound₁ bound₂ free hb hbound
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model,equalityAtom_model]
    exact alignedNeighborhood x y _ _ _ _ reserve ha' hb' hzy hzx
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model]
    exact alignedMembership x y _ _ _ _ hb' ha'

theorem alignedNegativeAtom (x y r a b bound₁ bound₂ free base₁ base₂ reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (hbound : ∀ i : M, LabelAligned x y bound₁.[i] bound₂.[i])
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],bound₁,free,base₁,reserve])
      (F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],bound₂,free,base₂,reserve]) := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv]
  exact targetPremiseRewrite_neg _ _ _
    (alignedPositiveAtom x y r a b bound₁ bound₂ free base₁ base₂ reserve hr ha hb hbound hzy hzx)

/-- Arbitrary aligned bound stacks transport any internal quantifier-free
source formula, under primitive equality. -/
theorem alignedQuantifierFree (p x y bound₁ bound₂ free base₁ base₂ reserve : M)
    (hp : IsUFormula SourceL p) (hqf : InternalQuantifierFree p)
    (hbound : ∀ i : M, LabelAligned x y bound₁.[i] bound₂.[i])
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    TargetPremiseRewrite (eqValue y x)
      (F fixedFormulaTranslation ![p,bound₁,free,base₁,reserve])
      (F fixedFormulaTranslation ![p,bound₂,free,base₂,reserve]) := by
  let e := pair bound₁ (pair free (pair base₁ reserve))
  let e' := pair bound₂ (pair free (pair base₂ reserve))
  let E := eqValue y x
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₂ (impValue : M → M → M) := (numericalCalc (M := M)).imp_defined.to_definable
  haveI : 𝚺₁-Predicate (TargetProvable : M → Prop) := targetProvable_definable
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q →
      TargetPremiseRewrite E (positiveTranslation e q) (positiveTranslation e' q)) := by
    unfold TargetPremiseRewrite
    definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q →
      TargetPremiseRewrite E (positiveTranslation e q) (positiveTranslation e' q) := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv _
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      dsimp only [e,e',E]
      rw [positiveTranslation_model,positiveTranslation_model]
      exact alignedPositiveAtom x y r a b bound₁ bound₂ free base₁ base₂ reserve hr ha hb hbound hzy hzx
    · intro arity r v hr hv _
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      dsimp only [e,e',E]
      rw [positiveTranslation_model,positiveTranslation_model]
      exact alignedNegativeAtom x y r a b bound₁ bound₂ free base₁ base₂ reserve hr ha hb hbound hzy hzx
    · intro _
      dsimp only [e,e',E]
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
      exact targetPremiseRewrite_refl _ _
    · intro _
      dsimp only [e,e',E]
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
      exact targetPremiseRewrite_refl _ _
    · intro a b ha hb iha ihb hfree
      have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree)
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree)
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_and _ _ _ _ _ _ ha hb,fixedFormulaTranslation_and _ _ _ _ _ _ ha hb]
      exact targetPremiseRewrite_and _ _ _ _ _ ih1 ih2
    · intro a b ha hb iha ihb hfree
      have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree)
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree)
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_or _ _ _ _ _ _ ha hb,fixedFormulaTranslation_or _ _ _ _ _ _ ha hb]
      exact targetPremiseRewrite_imp _ _ _ _ _ (targetPremiseRewrite_neg _ _ _ ih1) ih2
    · intro a ha ih hfree
      exact False.elim (internalQuantifierFree_not_all a hfree)
    · intro a ha ih hfree
      exact False.elim (internalQuantifierFree_not_ex a hfree)
  have hh := hall p hp hqf
  dsimp only [e,e',E] at hh
  simpa only [positiveTranslation_model] using hh

#print axioms alignedQuantifierFree
#print axioms alignedTermLabels
#print axioms alignedPositiveAtom
#print axioms alignedNegativeAtom
#print axioms alignedMembership
#print axioms alignedNeighborhood
end models
end PA194ModelLogic
