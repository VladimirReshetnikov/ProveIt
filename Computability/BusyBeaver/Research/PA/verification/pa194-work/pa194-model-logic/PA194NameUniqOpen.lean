import PA194GuardedUniqProp
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

theorem nameOfUniq_open {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) (j k : V) :
    GDerivable T (insert (neg SourceL (tr (uniq t)))
      (insert (neg SourceL (tr (peq (^&k) t)))
        (insert (tr (neg PA194PAeq.language (peq (^&j) t) ^⋎ peq (^&j) (^&k))) (∅ : V)))) := by
  have hj : IsSemiterm PA194PAeq.language 0 (^&j) := by simp
  have hk : IsSemiterm PA194PAeq.language 0 (^&k) := by simp
  have hA := peq_valid hj ht
  have hB := peq_valid hk ht
  have hC := peq_valid hj hk
  have hnegA := IsSemiformula.neg_iff.mpr hA
  have hnegB := IsSemiformula.neg_iff.mpr hB
  have hrest := IsSemiformula.or.mpr ⟨hnegB,hC⟩
  have hprop := guarded_uniq_prop (T := T) (tr_valid hA) (tr_valid hB) (tr_valid hC)
  have hmatrix : GDerivable T (insert (neg SourceL (tr (substs1 PA194PAeq.language (^&k) (uniqAtOuter t j))))
      (insert (neg SourceL (tr (peq (^&k) t)))
        (insert (tr (neg PA194PAeq.language (peq (^&j) t) ^⋎ peq (^&j) (^&k))) (∅ : V)))) := by
    rw [uniq_inner_instance ht j k, tr_or hnegA hrest, tr_neg hA,
      tr_or hnegB hC, tr_neg hB, tr_or hnegA hC, tr_neg hA]
    exact hprop
  have hinner := guarded_tr_all_left (T := T) (uniqAtOuter_valid ht j) k hmatrix
  rw [←uniq_outer_instance ht j] at hinner
  have houter : IsSemiformula PA194PAeq.language 1 (^∀ (uniqMatrix t)) :=
    IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using uniqMatrix_valid ht)
  have hout := guarded_tr_all_left (T := T) houter j hinner
  simpa only [uniq,uniqMatrix] using hout
#print axioms nameOfUniq_open
end generic
end PA194GuardedCompiler
