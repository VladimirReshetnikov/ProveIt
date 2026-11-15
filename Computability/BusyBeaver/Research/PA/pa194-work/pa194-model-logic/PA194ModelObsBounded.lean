import PA194ModelObsAligned
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
local instance obsBoundedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance obsBoundedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance obsBoundedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance obsBoundedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance obsBoundedLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance obsBoundedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






def stageLabelsAligned (stage₁ stage₂ : M → M) (ceiling x y n : M) : Prop :=
  ∀ i ≤ ceiling, LabelAligned x y (stage₁ n).[i] (stage₂ n).[i]

theorem stageLabelsAligned_definable (stage₁ stage₂ : M → M) (ceiling x y : M)
    (h₁ : 𝚺₁-Function₁ stage₁) (h₂ : 𝚺₁-Function₁ stage₂) :
    𝚺₁-Predicate (stageLabelsAligned stage₁ stage₂ ceiling x y) := by
  haveI := h₁
  haveI := h₂
  unfold stageLabelsAligned LabelAligned
  definability

/-- Equal binder allocations preserve bounded pointwise label alignment. -/
theorem allocatedBound_aligned (ceiling base initial₁ initial₂ x y : M)
    (hinit : ∀ i ≤ ceiling, LabelAligned x y initial₁.[i] initial₂.[i])
    (n : M) (hn : n ≤ ceiling) :
    ∀ i ≤ ceiling, LabelAligned x y
      (F allocateBound ![n,base,initial₁]).[i] (F allocateBound ![n,base,initial₂]).[i] := by
  let stage₁ : M → M := fun n => F allocateBound ![n,base,initial₁]
  let stage₂ : M → M := fun n => F allocateBound ![n,base,initial₂]
  haveI : 𝚺₁-Predicate (stageLabelsAligned stage₁ stage₂ ceiling x y) :=
    stageLabelsAligned_definable stage₁ stage₂ ceiling x y
      (PA194CodeInstance.unary_of_three allocateBound base initial₁)
      (PA194CodeInstance.unary_of_three allocateBound base initial₂)
  have hdef : 𝚺₁-Predicate (fun n : M => n ≤ ceiling → stageLabelsAligned stage₁ stage₂ ceiling x y n) := by definability
  have hall : ∀ n : M, n ≤ ceiling → stageLabelsAligned stage₁ stage₂ ceiling x y n := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _ i hi
      change LabelAligned x y (F allocateBound ![0,base,initial₁]).[i]
        (F allocateBound ![0,base,initial₂]).[i]
      rw [allocateBound_zero,allocateBound_zero]
      exact hinit i hi
    case succ n ih =>
      intro hn i hi
      have hn' : n ≤ ceiling := le_trans (le_of_lt (lt_add_one n)) hn
      change LabelAligned x y (F allocateBound ![n+1,base,initial₁]).[i]
        (F allocateBound ![n+1,base,initial₂]).[i]
      rw [allocateBound_succ,allocateBound_succ]
      rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
      · rw [nth_zero,nth_zero]
        simp [fstIdx,LabelAligned]
      · rw [nth_succ,nth_succ]
        have hj : j ≤ ceiling := le_trans (le_of_lt (lt_add_one j)) hi
        have hp := ih hn' j hj
        change LabelAligned x y (F allocateBound ![n,base,initial₁]).[j]
          (F allocateBound ![n,base,initial₂]).[j] at hp
        simpa [sndIdx] using hp
  exact hall n hn

theorem termLabels_aligned_bounded (x y t bound₁ bound₂ free K : M)
    (ht : IsUTerm SourceL t) (htK : t ≤ K)
    (hbound : ∀ i ≤ K, LabelAligned x y bound₁.[i] bound₂.[i]) :
    LabelAligned x y (F termLabelCode ![t,bound₁,free]) (F termLabelCode ![t,bound₂,free]) := by
  rcases PA194TermShiftModel.term_cases ht with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [termLabel_bound_nth,termLabel_bound_nth]
    exact hbound i (le_trans (le_of_lt (boundVariable_index_lt i)) htK)
  · rw [termLabel_free_nth,termLabel_free_nth]
    exact Or.inl rfl

theorem termIndex_bounded (t K : M) (htK : t ≤ K) :
    ∀ i, (t = ^#i ∨ t = ^&i) → i ≤ K := by
  intro i hi
  rcases hi with h | h <;> subst t
  · exact le_trans (le_of_lt (boundVariable_index_lt i)) htK
  · exact le_trans (le_of_lt (freeVariable_index_lt i)) htK

theorem observationalPositiveAtom_bounded (x y r a b bound₁ bound₂ free base reserve K : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (haK : a ≤ K) (hbK : b ≤ K)
    (hbound : ∀ i ≤ K, LabelAligned x y bound₁.[i] bound₂.[i])
    (hbound₁ : ∀ i ≤ K, bound₁.[i] < reserve) (hbound₂ : ∀ i ≤ K, bound₂.[i] < reserve)
    (hfree : ∀ i ≤ K, free.[i] < reserve)
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    TargetPremiseRewrite (neighborhoodValue y x reserve)
      (F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],bound₁,free,base,reserve])
      (F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],bound₂,free,base,reserve]) := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have ha' := termLabels_aligned_bounded x y a bound₁ bound₂ free K ha haK hbound
  have hb' := termLabels_aligned_bounded x y b bound₁ bound₂ free K hb hbK hbound
  have hfa₁ := termLabel_lt_reserved ha bound₁ free K reserve hbound₁ hfree (termIndex_bounded a K haK)
  have hfa₂ := termLabel_lt_reserved ha bound₂ free K reserve hbound₂ hfree (termIndex_bounded a K haK)
  have hfb₁ := termLabel_lt_reserved hb bound₁ free K reserve hbound₁ hfree (termIndex_bounded b K hbK)
  have hfb₂ := termLabel_lt_reserved hb bound₂ free K reserve hbound₂ hfree (termIndex_bounded b K hbK)
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model,equalityAtom_model]
    exact observationalNeighborhood x y _ _ _ _ reserve ha' hb'
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model]
    exact observationalMembership x y _ _ _ _ reserve hb' ha' hzy hzx (ne_of_gt hfa₁) (ne_of_gt hfb₂)

theorem observationalNegativeAtom_bounded (x y r a b bound₁ bound₂ free base reserve K : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b)
    (haK : a ≤ K) (hbK : b ≤ K)
    (hbound : ∀ i ≤ K, LabelAligned x y bound₁.[i] bound₂.[i])
    (hbound₁ : ∀ i ≤ K, bound₁.[i] < reserve) (hbound₂ : ∀ i ≤ K, bound₂.[i] < reserve)
    (hfree : ∀ i ≤ K, free.[i] < reserve)
    (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    TargetPremiseRewrite (neighborhoodValue y x reserve)
      (F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],bound₁,free,base,reserve])
      (F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],bound₂,free,base,reserve]) := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv]
  exact targetPremiseRewrite_neg _ _ _
    (observationalPositiveAtom_bounded x y r a b bound₁ bound₂ free base reserve K hr ha hb
      haK hbK hbound hbound₁ hbound₂ hfree hzy hzx)

#print axioms observationalPositiveAtom_bounded
#print axioms observationalNegativeAtom_bounded
#print axioms stageLabelsAligned_definable
#print axioms allocatedBound_aligned
end models
end PA194ModelLogic
