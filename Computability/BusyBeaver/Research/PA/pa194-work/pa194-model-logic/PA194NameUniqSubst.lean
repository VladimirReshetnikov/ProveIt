import PA194GuardedUniversalLeft
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def uniqMatrix (t : V) : V :=
  neg PA194PAeq.language (peq (^#(1 : V)) (termBShift PA194PAeq.language (termBShift PA194PAeq.language t))) ^⋎
    (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language (termBShift PA194PAeq.language t))) ^⋎
      peq (^#(1 : V)) (^#(0 : V)))
noncomputable def uniqAtOuter (t j : V) : V :=
  neg PA194PAeq.language (peq (^&j) (termBShift PA194PAeq.language t)) ^⋎
    (neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language t)) ^⋎
      peq (^&j) (^#(0 : V)))

theorem uniqMatrix_valid {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) :
    IsSemiformula PA194PAeq.language 2 (uniqMatrix t) := by
  have hb : IsSemiterm PA194PAeq.language 2 (termBShift PA194PAeq.language (termBShift PA194PAeq.language t)) := by
    simpa [one_add_one_eq_two] using IsSemiterm.termBShift (bShift_valid ht)
  unfold uniqMatrix
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) hb),
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) hb),peq_valid (by simp) (by simp)⟩⟩

theorem substs_peq {n m a b w : V} (ha : IsSemiterm PA194PAeq.language n a)
    (hb : IsSemiterm PA194PAeq.language n b) (hw : IsSemitermVec PA194PAeq.language n m w) :
    subst PA194PAeq.language w (peq a b) = peq (termSubst PA194PAeq.language w a) (termSubst PA194PAeq.language w b) := by
  have hv : IsUTermVec PA194PAeq.language 2 (?[a,b] : V) := by simp [ha.isUTerm,hb.isUTerm]
  show subst PA194PAeq.language w (^rel (2 : V) 0 (?[a,b] : V)) = _
  rw [substs_rel isRel_eq hv, termSubstVec_cons₂ ha.isUTerm hb.isUTerm]
  rfl

theorem uniq_outer_instance {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) (j : V) :
    substs1 PA194PAeq.language (^&j) (^∀ (uniqMatrix t)) = ^∀ (uniqAtOuter t j) := by
  have hb : IsSemiterm PA194PAeq.language 2 (termBShift PA194PAeq.language (termBShift PA194PAeq.language t)) := by
    simpa [one_add_one_eq_two] using IsSemiterm.termBShift (bShift_valid ht)
  have h0 : IsSemiterm PA194PAeq.language 2 (^#(0 : V)) := by simp
  have h1 : IsSemiterm PA194PAeq.language 2 (^#(1 : V)) := by simp
  have hvec : IsSemitermVec PA194PAeq.language 1 0 (?[^&j] : V) := by simp
  have hq : IsSemitermVec PA194PAeq.language 2 1 (qVec PA194PAeq.language (?[^&j] : V)) :=
    qVecA_singleton_valid (by simp)
  have he0 := peq_valid h0 hb
  have he1 := peq_valid h1 hb
  have heq := peq_valid h1 h0
  have hr := IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr he0,heq⟩
  rw [substs1_all (uniqMatrix_valid ht)]
  unfold uniqMatrix uniqAtOuter
  rw [substs_or (IsSemiformula.neg_iff.mpr he1).isUFormula hr.isUFormula,
    substs_neg he1 hq, substs_or (IsSemiformula.neg_iff.mpr he0).isUFormula heq.isUFormula,
    substs_neg he0 hq, substs_peq h1 hb hq, substs_peq h0 hb hq, substs_peq h1 h0 hq]
  have hbb : termSubst PA194PAeq.language (qVec PA194PAeq.language (?[^&j] : V))
      (termBShift PA194PAeq.language (termBShift PA194PAeq.language t)) = termBShift PA194PAeq.language t := by
    rw [substs_qVec_bShift (bShift_valid ht) hvec, substs_cons_bShift ht, substs_nil ht]
  rw [hbb, termSubst_bvar, termSubst_bvar]
  simp [qVecA_singleton (by simp : IsSemiterm PA194PAeq.language 0 (^&j : V))]
#print axioms uniqMatrix_valid
#print axioms substs_peq
#print axioms uniq_outer_instance
end generic
end PA194GuardedCompiler
