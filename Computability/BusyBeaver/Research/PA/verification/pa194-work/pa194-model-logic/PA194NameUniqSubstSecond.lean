import PA194NameUniqSubst
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem uniqAtOuter_valid {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) (j : V) :
    IsSemiformula PA194PAeq.language 1 (uniqAtOuter t j) := by
  unfold uniqAtOuter
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (bShift_valid ht)),
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (bShift_valid ht)),
      peq_valid (by simp) (by simp)⟩⟩

theorem uniq_inner_instance {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) (j k : V) :
    substs1 PA194PAeq.language (^&k) (uniqAtOuter t j) =
      neg PA194PAeq.language (peq (^&j) t) ^⋎
        (neg PA194PAeq.language (peq (^&k) t) ^⋎ peq (^&j) (^&k)) := by
  have hj : IsSemiterm PA194PAeq.language 1 (^&j) := by simp
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have hb := bShift_valid ht
  have e1 := peq_valid hj hb
  have e0 := peq_valid h0 hb
  have eq := peq_valid hj h0
  have rest := IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr e0,eq⟩
  unfold uniqAtOuter
  rw [substs1_orA (IsSemiformula.neg_iff.mpr e1) rest,
    substs1_negA e1 (by simp), substs1_orA (IsSemiformula.neg_iff.mpr e0) eq,
    substs1_negA e0 (by simp), substs1_peq hj hb, substs1_peq h0 hb, substs1_peq hj h0]
  simp [termSubst_fvar,termSubst_bvar,substs_cons_bShift ht,substs_nil ht]
#print axioms uniqAtOuter_valid
#print axioms uniq_inner_instance
end generic
end PA194GuardedCompiler
