import PA194GuardedSymmetrySyntax
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def transitivityMatrix : V := neg PA194PAeq.language (peq (^#(2 : V)) (^#(1 : V))) ^⋎
  (neg PA194PAeq.language (peq (^#(1 : V)) (^#(0 : V))) ^⋎ peq (^#(2 : V)) (^#(0 : V)))
noncomputable def transitivityTwo (x : V) : V := neg PA194PAeq.language (peq (^&x) (^#(1 : V))) ^⋎
  (neg PA194PAeq.language (peq (^#(1 : V)) (^#(0 : V))) ^⋎ peq (^&x) (^#(0 : V)))
noncomputable def transitivityOne (x y : V) : V := neg PA194PAeq.language (peq (^&x) (^&y)) ^⋎
  (neg PA194PAeq.language (peq (^&y) (^#(0 : V))) ^⋎ peq (^&x) (^#(0 : V)))

theorem transitivityMatrix_valid : IsSemiformula PA194PAeq.language 3 (transitivityMatrix : V) := by
  have h23 : (2 : V) < 3 := by norm_num
  unfold transitivityMatrix
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp [h23]) (by simp [h23])),
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp [h23]) (by simp [h23])),peq_valid (by simp [h23]) (by simp [h23])⟩⟩
theorem transitivityTwo_valid (x : V) : IsSemiformula PA194PAeq.language 2 (transitivityTwo x) := by
  unfold transitivityTwo
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)),
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)),peq_valid (by simp) (by simp)⟩⟩
theorem transitivityOne_valid (x y : V) : IsSemiformula PA194PAeq.language 1 (transitivityOne x y) := by
  unfold transitivityOne
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)),
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)),peq_valid (by simp) (by simp)⟩⟩

theorem transitivity_quote : (⌜PA194PAeq.transitivity⌝ : V) = ^∀ (^∀ (^∀ (transitivityMatrix : V))) := by
  change (⌜∀⁰ (∀⁰ (∀⁰ PA194PAeq.implies (PA194PAeq.eq (.bvar 2) (.bvar 1))
    (PA194PAeq.implies (PA194PAeq.eq (.bvar 1) (.bvar 0)) (PA194PAeq.eq (.bvar 2) (.bvar 0)))))⌝ : V) = _
  rw [Semiformula.quote_all,Semiformula.quote_all,Semiformula.quote_all]
  congr 3
  change (⌜(PA194PAeq.eq (.bvar 2) (.bvar 1)).neg ⋎
    ((PA194PAeq.eq (.bvar 1) (.bvar 0)).neg ⋎ (PA194PAeq.eq (.bvar 2) (.bvar 0)))⌝ : V) = _
  rw [Semiformula.quote_or,Semiformula.quote_or]
  simp [PA194PAeq.eq,transitivityMatrix,peq,Semiformula.quote_rel,
    SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  refine ⟨?_, ?_, ?_⟩
  · change (⌜(LO.FirstOrder.Semiformula.nrel PA194PAeq.Rel.eq ![(.bvar 2),(.bvar 1)] : Semiproposition PA194PAeq.language 3)⌝ : V) = _
    rw [Semiformula.quote_nrel]
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
    rfl
  · change (⌜(LO.FirstOrder.Semiformula.nrel PA194PAeq.Rel.eq ![(.bvar 1),(.bvar 0)] : Semiproposition PA194PAeq.language 3)⌝ : V) = _
    rw [Semiformula.quote_nrel]
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
    rfl
  · rfl

theorem qVecA_pair_variable (x : V) :
    qVec PA194PAeq.language (?[ ^#(0 : V), ^&x] : V) = (?[ ^#(0 : V), ^#(1 : V), ^&x] : V) := by
  unfold qVec
  rw [show len (?[ ^#(0 : V), ^&x] : V) = 2 by simp [one_add_one_eq_two],
    termBShiftVec_cons₂ (show IsUTerm PA194PAeq.language (^#(0 : V)) by simp)
      (show IsUTerm PA194PAeq.language (^&x) by simp),termBShift_bvar,termBShift_fvar]
  simp

theorem transitivity_open_first (x : V) :
    substs1 PA194PAeq.language (^&x) (^∀ (^∀ (transitivityMatrix : V))) = ^∀ (^∀ (transitivityTwo x)) := by
  have hp : IsSemiformula PA194PAeq.language 2 (^∀ (transitivityMatrix : V)) :=
    IsSemiformula.all.mpr (by simpa [show (2 : V) + 1 = 3 by norm_num] using (transitivityMatrix_valid (V := V)))
  rw [substs1_all hp, qVecA_singleton (show IsSemiterm PA194PAeq.language 0 (^&x) by simp), termBShift_fvar,
    substs_all transitivityMatrix_valid.isUFormula, qVecA_pair_variable]
  congr 2
  have h23 : (2 : V) < 3 := by norm_num
  have ha : IsSemiformula PA194PAeq.language 3 (peq (^#(2 : V)) (^#(1 : V))) := peq_valid (by simp [h23]) (by simp)
  have hb : IsSemiformula PA194PAeq.language 3 (peq (^#(1 : V)) (^#(0 : V))) := peq_valid (by simp) (by simp)
  have hc : IsSemiformula PA194PAeq.language 3 (peq (^#(2 : V)) (^#(0 : V))) := peq_valid (by simp [h23]) (by simp)
  have hw : IsSemitermVec PA194PAeq.language 3 2 (?[ ^#(0 : V), ^#(1 : V), ^&x] : V) := by
    have heq : (2 : V) + 1 = 3 := by norm_num
    rw [← heq, IsSemitermVec.cons_iff]
    constructor
    · simp
    · rw [← one_add_one_eq_two, IsSemitermVec.cons_iff]
      constructor <;> simp
  unfold transitivityMatrix transitivityTwo
  rw [substs_or (IsSemiformula.neg_iff.mpr ha).isUFormula (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hb,hc⟩).isUFormula,
    substs_or (IsSemiformula.neg_iff.mpr hb).isUFormula hc.isUFormula,substs_neg ha hw,substs_neg hb hw,
    subst_peq_general (show IsSemiterm PA194PAeq.language 3 (^#(2 : V)) by simp [h23]) (show IsSemiterm PA194PAeq.language 3 (^#(1 : V)) by simp),
    subst_peq_general (show IsSemiterm PA194PAeq.language 3 (^#(1 : V)) by simp) (show IsSemiterm PA194PAeq.language 3 (^#(0 : V)) by simp),
    subst_peq_general (show IsSemiterm PA194PAeq.language 3 (^#(2 : V)) by simp [h23]) (show IsSemiterm PA194PAeq.language 3 (^#(0 : V)) by simp)]
  simp [termSubst_bvar]

theorem transitivity_open_second (x y : V) :
    substs1 PA194PAeq.language (^&y) (^∀ (transitivityTwo x)) = ^∀ (transitivityOne x y) := by
  rw [substs1_all (transitivityTwo_valid x),qVecA_singleton (show IsSemiterm PA194PAeq.language 0 (^&y) by simp),termBShift_fvar]
  congr 1
  have ha : IsSemiformula PA194PAeq.language 2 (peq (^&x) (^#(1 : V))) := peq_valid (by simp) (by simp)
  have hb : IsSemiformula PA194PAeq.language 2 (peq (^#(1 : V)) (^#(0 : V))) := peq_valid (by simp) (by simp)
  have hc : IsSemiformula PA194PAeq.language 2 (peq (^&x) (^#(0 : V))) := peq_valid (by simp) (by simp)
  have hw : IsSemitermVec PA194PAeq.language 2 1 (?[ ^#(0 : V), ^&y] : V) := by simp
  unfold transitivityTwo transitivityOne
  rw [substs_or (IsSemiformula.neg_iff.mpr ha).isUFormula (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hb,hc⟩).isUFormula,
    substs_or (IsSemiformula.neg_iff.mpr hb).isUFormula hc.isUFormula,substs_neg ha hw,substs_neg hb hw,
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^&x) by simp) (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp),
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp) (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp),
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^&x) by simp) (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp)]
  simp [termSubst_bvar,termSubst_fvar]

theorem transitivity_open_third (x y z : V) :
    substs1 PA194PAeq.language (^&z) (transitivityOne x y) =
      neg PA194PAeq.language (peq (^&x) (^&y)) ^⋎
      (neg PA194PAeq.language (peq (^&y) (^&z)) ^⋎ peq (^&x) (^&z)) := by
  have ha : IsSemiformula PA194PAeq.language 1 (peq (^&x) (^&y)) := peq_valid (by simp) (by simp)
  have hb : IsSemiformula PA194PAeq.language 1 (peq (^&y) (^#(0 : V))) := peq_valid (by simp) (by simp)
  have hc : IsSemiformula PA194PAeq.language 1 (peq (^&x) (^#(0 : V))) := peq_valid (by simp) (by simp)
  unfold transitivityOne
  rw [substs1_orA (IsSemiformula.neg_iff.mpr ha) (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hb,hc⟩),
    substs1_orA (IsSemiformula.neg_iff.mpr hb) hc,substs1_negA ha (by simp),substs1_negA hb (by simp),
    substs1_peq (by simp) (by simp),substs1_peq (by simp) (by simp),substs1_peq (by simp) (by simp)]
  simp [termSubst_bvar,termSubst_fvar]

#print axioms transitivity_quote
#print axioms qVecA_pair_variable
#print axioms transitivity_open_first
#print axioms transitivityMatrix_valid
#print axioms transitivity_open_second
#print axioms transitivity_open_third
end generic
end PA194GuardedCompiler
