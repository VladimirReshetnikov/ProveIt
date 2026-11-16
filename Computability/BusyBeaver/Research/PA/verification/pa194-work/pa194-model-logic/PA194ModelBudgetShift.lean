import PA194ModelFormulaTranslation
import PackedDecoderModel
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
local instance budgetShiftZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance budgetShiftOne : One M := ⟨F oneCode Fin.elim0⟩
local instance budgetShiftAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance budgetShiftMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance budgetShiftLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance budgetShiftIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelSub_shift (ceiling b d : M) :
    F subCode ![ceiling+d,b+d] = F subCode ![ceiling,b] := by
  rw [PackedDecoderModel.modelSubAsTsub,PackedDecoderModel.modelSubAsTsub]
  exact Arithmetic.add_sub_add ceiling b d

theorem boundValue_shift (params ceiling base reserve b d : M) :
    boundValue (b+d) params (pair (ceiling+d) (pair base reserve)) =
      boundValue b params (pair ceiling (pair base reserve)) := by
  simp only [boundValue,pi₁_pair,pi₂_pair,boundAtBudget_model,modelSub_shift]

theorem labelValue_shift (ceiling base reserve b d : M) :
    labelValue (b+d) (pair (ceiling+d) (pair base reserve)) =
      labelValue b (pair ceiling (pair base reserve)) := by
  simp only [labelValue,pi₁_pair,pi₂_pair,labelAtBudget_model,modelSub_shift]

theorem atomValue_shift (tag r v b params ceiling base reserve d : M) :
    atomValue tag r v (b+d) params (pair (ceiling+d) (pair base reserve)) =
      atomValue tag r v b params (pair ceiling (pair base reserve)) := by
  simp only [atomValue,pi₂_pair,boundValue_shift]

noncomputable def budgetShiftReference (params ceiling base reserve d p b : M) : M :=
  formulaReference params (pair (ceiling+d) (pair base reserve)) p (b+d)

theorem budgetShiftReference_definable (params ceiling base reserve d : M) :
    𝚺₁-Function₂ (budgetShiftReference params ceiling base reserve d) := by
  haveI := formulaReference_definable (M := M) params (pair (ceiling+d) (pair base reserve))
  unfold budgetShiftReference
  definability

theorem budgetShiftReference_recurrence (params ceiling base reserve d : M) :
    FormulaRecurrenceF (budgetShiftReference params ceiling base reserve d)
      params (pair ceiling (pair base reserve)) where
  positive := by
    intro r v b hr hv
    change formulaReference params (pair (ceiling+d) (pair base reserve)) _ (b+d) = _
    rw [(formulaReference_recurrence params _).positive r v (b+d) hr hv,atomValue_shift]
  negative := by
    intro r v b hr hv
    change formulaReference params (pair (ceiling+d) (pair base reserve)) _ (b+d) = _
    rw [(formulaReference_recurrence params _).negative r v (b+d) hr hv,atomValue_shift]
  truth := by
    intro b
    exact (formulaReference_recurrence params _).truth (b+d)
  falsum := by
    intro b
    exact (formulaReference_recurrence params _).falsum (b+d)
  andRule := by
    intro p q b hp hq
    exact (formulaReference_recurrence params _).andRule p q (b+d) hp hq
  orRule := by
    intro p q b hp hq
    exact (formulaReference_recurrence params _).orRule p q (b+d) hp hq
  allRule := by
    intro p b hp
    change formulaReference params (pair (ceiling+d) (pair base reserve)) _ ((b+1)+d) = _
    have he : (b+1)+d = (b+d)+1 := by ac_rfl
    rw [he,(formulaReference_recurrence params _).allRule p (b+d) hp,←he,labelValue_shift]
    rfl
  exRule := by
    intro p b hp
    change formulaReference params (pair (ceiling+d) (pair base reserve)) _ ((b+1)+d) = _
    have he : (b+1)+d = (b+d)+1 := by ac_rfl
    rw [he,(formulaReference_recurrence params _).exRule p (b+d) hp,←he,labelValue_shift]
    rfl

/-- Shifting the remaining and initial budgets by the same model amount preserves
translation on every internally valid formula when its code fits the budget. -/
theorem formulaReference_budget_shift (p b params ceiling base reserve d : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) (hpb : p ≤ b) :
    formulaReference params (pair ceiling (pair base reserve)) p b =
      formulaReference params (pair (ceiling+d) (pair base reserve)) p (b+d) := by
  have h := boundedAgreementF_of_recurrence
    (budgetShiftReference params ceiling base reserve d) b params (pair ceiling (pair base reserve))
    (budgetShiftReference_definable params ceiling base reserve d)
    (budgetShiftReference_recurrence params ceiling base reserve d) p hp b (le_refl b) hpb
  rw [formulaHistory_reference p b params (pair ceiling (pair base reserve)) hp hpb] at h
  exact h

theorem fixedFormulaTranslation_reference_bigger (p b bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) (hpb : p ≤ b) :
    F fixedFormulaTranslation ![p,bound,free,base,reserve] =
      formulaReference (pair bound free) (pair b (pair base reserve)) p b := by
  rw [fixedFormulaTranslation_correct p bound free base reserve hp]
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hpb
  rw [hd]
  exact formulaReference_budget_shift p p _ p base reserve d hp (le_refl p)

theorem fixedFormulaTranslation_or (p q bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    F fixedFormulaTranslation ![p ^⋎ q,bound,free,base,reserve] =
      impValue (negValue (F fixedFormulaTranslation ![p,bound,free,base,reserve]))
        (F fixedFormulaTranslation ![q,bound,free,base,reserve]) := by
  have hs : IsUFormula M6.PA.RelationalSource.language (p ^⋎ q) := by
    simpa only [IsUFormula.or] using And.intro hp hq
  have hl : p ≤ p ^⋎ q := le_of_lt <| lt_of_le_of_lt
    (le_trans (le_pair_left p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
  have hr : q ≤ p ^⋎ q := le_of_lt <| lt_of_le_of_lt
    (le_trans (le_pair_right p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hs,
    fixedFormulaTranslation_reference_bigger p (p ^⋎ q) bound free base reserve hp hl,
    fixedFormulaTranslation_reference_bigger q (p ^⋎ q) bound free base reserve hq hr]
  exact (formulaReference_recurrence (pair bound free) (pair (p ^⋎ q) (pair base reserve))).orRule p q (p ^⋎ q) hp hq

theorem fixedFormulaTranslation_and (p q bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    F fixedFormulaTranslation ![p ^⋏ q,bound,free,base,reserve] =
      conjValue (F fixedFormulaTranslation ![p,bound,free,base,reserve])
        (F fixedFormulaTranslation ![q,bound,free,base,reserve]) := by
  have hs : IsUFormula M6.PA.RelationalSource.language (p ^⋏ q) := by
    simpa only [IsUFormula.and] using And.intro hp hq
  have hl : p ≤ p ^⋏ q := le_of_lt <| lt_of_le_of_lt
    (le_trans (le_pair_left p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
  have hr : q ≤ p ^⋏ q := le_of_lt <| lt_of_le_of_lt
    (le_trans (le_pair_right p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hs,
    fixedFormulaTranslation_reference_bigger p (p ^⋏ q) bound free base reserve hp hl,
    fixedFormulaTranslation_reference_bigger q (p ^⋏ q) bound free base reserve hq hr]
  exact (formulaReference_recurrence (pair bound free) (pair (p ^⋏ q) (pair base reserve))).andRule p q (p ^⋏ q) hp hq

#print axioms fixedFormulaTranslation_reference_bigger
#print axioms fixedFormulaTranslation_or
#print axioms fixedFormulaTranslation_and
#print axioms formulaReference_budget_shift
#print axioms budgetShiftReference_recurrence
#print axioms budgetShiftReference_definable
#print axioms modelSub_shift
#print axioms boundValue_shift
#print axioms labelValue_shift
#print axioms atomValue_shift
end models
end PA194ModelLogic
