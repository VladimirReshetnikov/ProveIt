import PA194ModelBudgetShift
import PA194ModelSourcePath
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
local instance binderAllocationShiftZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance binderAllocationShiftOne : One M := ⟨F oneCode Fin.elim0⟩
local instance binderAllocationShiftAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance binderAllocationShiftMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance binderAllocationShiftLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance binderAllocationShiftIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def shiftedAllocate : Code 3 :=
  PA194TargetStep.app3 allocateBound (unary .succ (.proj 0)) (.proj 1) (.proj 2)

theorem shiftedAllocate_model (j base initial : M) :
    F shiftedAllocate ![j,base,initial] = F allocateBound ![j+1,base,initial] := by
  simp only [shiftedAllocate,PA194TargetStep.app3_model,modelUnary,modelProjection,modelSucc,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_def,Matrix.cons_val_succ]

/-- Pushing the first label in advance commutes with allocating any model-valued
number of further labels. -/
theorem allocateBound_push_shift (base initial n : M) :
    F allocateBound ![n+1,base,initial] =
      F allocateBound ![n,base+1,pair base initial+1] := by
  haveI : 𝚺₁-Function₁ (fun k : M => F shiftedAllocate ![k,base,initial]) :=
    PA194CodeInstance.unary_of_three shiftedAllocate base initial
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base+1,pair base initial+1]) :=
    PA194CodeInstance.unary_of_three allocateBound (base+1) (pair base initial+1)
  have hdef' : 𝚺₁-Predicate (fun k : M => F shiftedAllocate ![k,base,initial] =
      F allocateBound ![k,base+1,pair base initial+1]) := by definability
  have hdef : 𝚺₁-Predicate (fun k : M => F allocateBound ![k+1,base,initial] =
      F allocateBound ![k,base+1,pair base initial+1]) := by
    simpa only [shiftedAllocate_model] using hdef'
  induction n using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero =>
    rw [allocateBound_zero,allocateBound_succ,allocateBound_zero]
    simp
  case succ n ih =>
    rw [allocateBound_succ,ih,allocateBound_succ]
    congr 2
    ac_rfl

theorem binderContext_bound (b ceiling initial free base reserve : M) (hb : b ≤ ceiling) :
    boundValue b (pair initial free) (pair (ceiling+1) (pair base reserve)) =
      boundValue b (pair (pair base initial+1) free) (pair ceiling (pair (base+1) reserve)) := by
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hb
  simp only [boundValue,pi₁_pair,pi₂_pair,boundAtBudget_model]
  rw [hd]
  have h0 := modelSubAdd b d
  change F subCode ![b+d,b] = d at h0
  have h1 := modelSubAdd b (d+1)
  change F subCode ![b+(d+1),b] = d+1 at h1
  rw [show b+d+1 = b+(d+1) by ac_rfl,h1,h0,allocateBound_push_shift]

theorem binderContext_label (b ceiling base reserve : M) (hb : b ≤ ceiling) :
    labelValue b (pair (ceiling+1) (pair base reserve)) =
      labelValue b (pair ceiling (pair (base+1) reserve)) := by
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hb
  simp only [labelValue,pi₁_pair,pi₂_pair,labelAtBudget_model]
  rw [hd]
  have h0 := modelSubAdd b d
  change F subCode ![b+d,b] = d at h0
  have h1 := modelSubAdd b (d+1)
  change F subCode ![b+(d+1),b] = d+1 at h1
  rw [show b+d+1 = b+(d+1) by ac_rfl,h1,h0]
  ac_rfl

theorem binderContext_atom (tag r v b ceiling initial free base reserve : M) (hb : b ≤ ceiling) :
    atomValue tag r v b (pair initial free) (pair (ceiling+1) (pair base reserve)) =
      atomValue tag r v b (pair (pair base initial+1) free) (pair ceiling (pair (base+1) reserve)) := by
  simp only [atomValue,pi₂_pair,binderContext_bound b ceiling initial free base reserve hb]

/-- Moving one already-consumed binder from the ceiling into the initial
stack/base preserves structural translation below the remaining ceiling. -/
theorem formulaReference_binder_context (p b ceiling initial free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) (hb : b ≤ ceiling) (hpb : p ≤ b) :
    formulaReference (pair initial free) (pair (ceiling+1) (pair base reserve)) p b =
      formulaReference (pair (pair base initial+1) free) (pair ceiling (pair (base+1) reserve)) p b := by
  let f := formulaReference (pair initial free) (pair (ceiling+1) (pair base reserve))
  let g := formulaReference (pair (pair base initial+1) free) (pair ceiling (pair (base+1) reserve))
  haveI : 𝚺₁-Function₂ f := formulaReference_definable _ _
  haveI : 𝚺₁-Function₂ g := formulaReference_definable _ _
  have hdef : 𝚺₁-Predicate (fun p : M => ∀ b ≤ ceiling, p ≤ b → f p b = g p b) := by definability
  have hf := formulaReference_recurrence (pair initial free) (pair (ceiling+1) (pair base reserve))
  have hg := formulaReference_recurrence (pair (pair base initial+1) free) (pair ceiling (pair (base+1) reserve))
  change f p b = g p b
  apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp b hb hpb
  · intro k r v hr hv b hb hcode
    have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
    subst k
    change formulaReference _ _ (^rel (2 : M) r v) b = formulaReference _ _ (^rel (2 : M) r v) b
    simp only [qqRel]
    rw [hf.positive r v b hr hv,hg.positive r v b hr hv]
    exact binderContext_atom 0 r v b ceiling initial free base reserve hb
  · intro k r v hr hv b hb hcode
    have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
    subst k
    change formulaReference _ _ (^nrel (2 : M) r v) b = formulaReference _ _ (^nrel (2 : M) r v) b
    simp only [qqNRel]
    rw [hf.negative r v b hr hv,hg.negative r v b hr hv]
    rw [binderContext_atom 1 r v b ceiling initial free base reserve hb]
  · intro b hb hcode
    exact (hf.truth b).trans (hg.truth b).symm
  · intro b hb hcode
    exact (hf.falsum b).trans (hg.falsum b).symm
  · intro p q hp hq ihp ihq b hb hcode
    have hl : p < pair (4 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
    have hr : q < pair (4 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
    have hcode' : pair (4 : M) (pair p q)+1 ≤ b := by simpa only [qqAnd] using hcode
    have hp' : p ≤ b := le_trans (le_of_lt hl) hcode'
    have hq' : q ≤ b := le_trans (le_of_lt hr) hcode'
    change formulaReference _ _ (p ^⋏ q) b = formulaReference _ _ (p ^⋏ q) b
    simp only [qqAnd]
    dsimp only [f,g] at ihp ihq
    rw [hf.andRule p q b hp hq,hg.andRule p q b hp hq,ihp b hb hp',ihq b hb hq']
  · intro p q hp hq ihp ihq b hb hcode
    have hl : p < pair (5 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
    have hr : q < pair (5 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
    have hcode' : pair (5 : M) (pair p q)+1 ≤ b := by simpa only [qqOr] using hcode
    have hp' : p ≤ b := le_trans (le_of_lt hl) hcode'
    have hq' : q ≤ b := le_trans (le_of_lt hr) hcode'
    change formulaReference _ _ (p ^⋎ q) b = formulaReference _ _ (p ^⋎ q) b
    simp only [qqOr]
    dsimp only [f,g] at ihp ihq
    rw [hf.orRule p q b hp hq,hg.orRule p q b hp hq,ihp b hb hp',ihq b hb hq']
  · intro p hp ih b hb hcode
    have hpos : (0 : M) < pair (6 : M) p+1 := by simp
    have hcode' : pair (6 : M) p+1 ≤ b := by simpa only [qqAll] using hcode
    rcases zero_or_succ b with (rfl | ⟨j,rfl⟩)
    · exact False.elim ((not_le_of_gt hpos) hcode')
    · have hc : p < pair (6 : M) p+1 := lt_of_le_of_lt (le_pair_right (6 : M) p) (lt_add_one _)
      have hpj : p ≤ j := lt_succ_iff_le.mp (lt_of_lt_of_le hc hcode')
      have hj : j ≤ ceiling := le_trans (le_of_lt (lt_add_one j)) hb
      change formulaReference _ _ (^∀ p) (j+1) = formulaReference _ _ (^∀ p) (j+1)
      simp only [qqAll]
      dsimp only [f,g] at ih
      rw [hf.allRule p j hp,hg.allRule p j hp,binderContext_label (j+1) ceiling base reserve hb,ih j hj hpj]
  · intro p hp ih b hb hcode
    have hpos : (0 : M) < pair (7 : M) p+1 := by simp
    have hcode' : pair (7 : M) p+1 ≤ b := by simpa only [qqExs] using hcode
    rcases zero_or_succ b with (rfl | ⟨j,rfl⟩)
    · exact False.elim ((not_le_of_gt hpos) hcode')
    · have hc : p < pair (7 : M) p+1 := lt_of_le_of_lt (le_pair_right (7 : M) p) (lt_add_one _)
      have hpj : p ≤ j := lt_succ_iff_le.mp (lt_of_lt_of_le hc hcode')
      have hj : j ≤ ceiling := le_trans (le_of_lt (lt_add_one j)) hb
      change formulaReference _ _ (^∃ p) (j+1) = formulaReference _ _ (^∃ p) (j+1)
      simp only [qqExs]
      dsimp only [f,g] at ih
      rw [hf.exRule p j hp,hg.exRule p j hp,binderContext_label (j+1) ceiling base reserve hb,ih j hj hpj]

theorem fixedFormulaTranslation_all (p bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F fixedFormulaTranslation ![^∀ p,bound,free,base,reserve] =
      allValue base (F fixedFormulaTranslation ![p,pair base bound+1,free,base+1,reserve]) := by
  have hs : IsUFormula M6.PA.RelationalSource.language (^∀ p) := by simpa only [IsUFormula.all] using hp
  have hpc : p ≤ pair (6 : M) p := le_pair_right (6 : M) p
  have hr := (formulaReference_recurrence (pair bound free)
    (pair (^∀ p) (pair base reserve))).allRule p (pair (6 : M) p) hp
  change formulaReference _ _ (^∀ p) (^∀ p) = _ at hr
  have hl : labelValue (^∀ p) (pair (^∀ p) (pair base reserve)) = base := by
    simp only [labelValue,pi₁_pair,pi₂_pair]
    exact (allocation_root (^∀ p) base bound).2
  change labelValue (pair (6 : M) p+1) (pair (^∀ p) (pair base reserve)) = base at hl
  have hc := formulaReference_binder_context p (pair (6 : M) p) (pair (6 : M) p)
    bound free base reserve hp (le_refl _) hpc
  change formulaReference (pair bound free) (pair (^∀ p) (pair base reserve)) p _ = _ at hc
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hs,hr,hl,hc,
    ←fixedFormulaTranslation_reference_bigger p (pair (6 : M) p)
      (pair base bound+1) free (base+1) reserve hp hpc]

theorem fixedFormulaTranslation_ex (p bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F fixedFormulaTranslation ![^∃ p,bound,free,base,reserve] =
      exValue base (F fixedFormulaTranslation ![p,pair base bound+1,free,base+1,reserve]) := by
  have hs : IsUFormula M6.PA.RelationalSource.language (^∃ p) := by simpa only [IsUFormula.ex] using hp
  have hpc : p ≤ pair (7 : M) p := le_pair_right (7 : M) p
  have hr := (formulaReference_recurrence (pair bound free)
    (pair (^∃ p) (pair base reserve))).exRule p (pair (7 : M) p) hp
  change formulaReference _ _ (^∃ p) (^∃ p) = _ at hr
  have hl : labelValue (^∃ p) (pair (^∃ p) (pair base reserve)) = base := by
    simp only [labelValue,pi₁_pair,pi₂_pair]
    exact (allocation_root (^∃ p) base bound).2
  change labelValue (pair (7 : M) p+1) (pair (^∃ p) (pair base reserve)) = base at hl
  have hc := formulaReference_binder_context p (pair (7 : M) p) (pair (7 : M) p)
    bound free base reserve hp (le_refl _) hpc
  change formulaReference (pair bound free) (pair (^∃ p) (pair base reserve)) p _ = _ at hc
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hs,hr,hl,hc,
    ←fixedFormulaTranslation_reference_bigger p (pair (7 : M) p)
      (pair base bound+1) free (base+1) reserve hp hpc]

#print axioms fixedFormulaTranslation_all
#print axioms fixedFormulaTranslation_ex
#print axioms formulaReference_binder_context
#print axioms binderContext_bound
#print axioms binderContext_label
#print axioms binderContext_atom
#print axioms allocateBound_push_shift
end models
end PA194ModelLogic
