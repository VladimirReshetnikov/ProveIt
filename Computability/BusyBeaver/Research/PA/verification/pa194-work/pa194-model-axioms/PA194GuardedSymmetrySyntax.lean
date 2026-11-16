import PA194UniqueVariableOpen
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def symmetryMatrix : V := neg PA194PAeq.language (peq (^#(1 : V)) (^#(0 : V))) ^⋎ peq (^#(0 : V)) (^#(1 : V))
noncomputable def symmetryOne (y : V) : V := neg PA194PAeq.language (peq (^&y) (^#(0 : V))) ^⋎ peq (^#(0 : V)) (^&y)

theorem symmetryMatrix_valid : IsSemiformula PA194PAeq.language 2 (symmetryMatrix : V) := by
  unfold symmetryMatrix
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)),peq_valid (by simp) (by simp)⟩
theorem symmetryOne_valid (y : V) : IsSemiformula PA194PAeq.language 1 (symmetryOne y) := by
  unfold symmetryOne
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)),peq_valid (by simp) (by simp)⟩
theorem symmetry_quote : (⌜PA194PAeq.symmetry⌝ : V) = ^∀ (^∀ (symmetryMatrix : V)) := by
  change (⌜∀⁰ (∀⁰ PA194PAeq.implies (PA194PAeq.eq (.bvar 1) (.bvar 0)) (PA194PAeq.eq (.bvar 0) (.bvar 1)))⌝ : V) = _
  rw [Semiformula.quote_all,Semiformula.quote_all]
  congr 2
  change (⌜(PA194PAeq.eq (.bvar 1) (.bvar 0)).neg ⋎ (PA194PAeq.eq (.bvar 0) (.bvar 1))⌝ : V) = _
  rw [Semiformula.quote_or]
  simp [PA194PAeq.eq,symmetryMatrix,peq,Semiformula.quote_nrel,Semiformula.quote_rel,
    SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  constructor
  · change (⌜(LO.FirstOrder.Semiformula.nrel PA194PAeq.Rel.eq ![(.bvar 1),(.bvar 0)] : Semiproposition PA194PAeq.language 2)⌝ : V) = _
    rw [Semiformula.quote_nrel]
    simp [SemitermVec.val_succ,Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
    rfl
  · rfl

theorem symmetry_open_first (y : V) :
    substs1 PA194PAeq.language (^&y) (^∀ (symmetryMatrix : V)) = ^∀ (symmetryOne y) := by
  rw [substs1_all symmetryMatrix_valid,qVecA_singleton (show IsSemiterm PA194PAeq.language 0 (^&y) by simp),termBShift_fvar]
  congr 1
  have ha : IsSemiformula PA194PAeq.language 2 (peq (^#(1 : V)) (^#(0 : V))) := peq_valid (by simp) (by simp)
  have hb : IsSemiformula PA194PAeq.language 2 (peq (^#(0 : V)) (^#(1 : V))) := peq_valid (by simp) (by simp)
  have hw : IsSemitermVec PA194PAeq.language 2 1 (?[ ^#(0 : V), ^&y] : V) := by simp
  unfold symmetryMatrix symmetryOne
  rw [substs_or (IsSemiformula.neg_iff.mpr ha).isUFormula hb.isUFormula,substs_neg ha hw,
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp),
    subst_peq_general (show IsSemiterm PA194PAeq.language 2 (^#(0 : V)) by simp)
      (show IsSemiterm PA194PAeq.language 2 (^#(1 : V)) by simp)]
  simp [termSubst_bvar]

theorem symmetry_open_second (y z : V) :
    substs1 PA194PAeq.language (^&z) (symmetryOne y) =
      neg PA194PAeq.language (peq (^&y) (^&z)) ^⋎ peq (^&z) (^&y) := by
  have ha : IsSemiformula PA194PAeq.language 1 (peq (^&y) (^#(0 : V))) := peq_valid (by simp) (by simp)
  have hb : IsSemiformula PA194PAeq.language 1 (peq (^#(0 : V)) (^&y)) := peq_valid (by simp) (by simp)
  unfold symmetryOne
  rw [substs1_orA (IsSemiformula.neg_iff.mpr ha) hb, substs1_negA ha (by simp),
    substs1_peq (by simp) (by simp),substs1_peq (by simp) (by simp)]
  simp [termSubst_bvar,termSubst_fvar]

#print axioms symmetry_quote
#print axioms symmetry_open_first
#print axioms symmetry_open_second
end generic
end PA194GuardedCompiler
