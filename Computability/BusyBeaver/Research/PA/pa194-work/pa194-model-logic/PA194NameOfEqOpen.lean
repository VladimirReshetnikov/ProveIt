import PA194NameOfUniq
import PA194NameRefl
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]

/-- The two explicit remaining fields used in the logical reduction of `nameOfEq`. -/
structure NameOfEqPrereqs : Prop where
  uVar : ∀ i : V, GDerivable T (insert (tr (uniq (^&i))) (∅ : V))
  atomTransfer : ∀ s₁ s₁' s₂ s₂' : V, IsSemiterm PA194PAeq.language 0 s₁ →
    IsSemiterm PA194PAeq.language 0 s₁' → IsSemiterm PA194PAeq.language 0 s₂ →
    IsSemiterm PA194PAeq.language 0 s₂' →
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (neg SourceL (tr (peq s₁ s₂))) (insert (tr (peq s₁' s₂')) (∅ : V)))))

variable {T}
theorem nameOfEq_open (N : NameOfEqPrereqs (V := V) T) {t : V}
    (ht : IsSemiterm PA194PAeq.language 0 t) (c j : V) :
    GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (tr (neg PA194PAeq.language (peq (^&j) (^&c)) ^⋎ peq (^&j) t)) (∅ : V))) := by
  have hc : IsSemiterm PA194PAeq.language 0 (^&c) := by simp
  have hj : IsSemiterm PA194PAeq.language 0 (^&j) := by simp
  let U : V := tr (uniq (^&c))
  let Q : V := tr (nameAll (^&c) (^&j))
  let R : V := tr (nameAll t t)
  let P : V := tr (peq (^&c) t)
  let E : V := tr (peq (^&j) (^&c))
  let S : V := tr (peq (^&j) t)
  let D : V := neg SourceL E ^⋎ S
  have hU : IsFormula SourceL U := tr_valid (uniq_valid hc)
  have hQ : IsFormula SourceL Q := tr_valid (nameAll_valid hc hj)
  have hR : IsFormula SourceL R := tr_valid (nameAll_valid ht ht)
  have hP : IsFormula SourceL P := tr_valid (peq_valid hc ht)
  have hE : IsFormula SourceL E := tr_valid (peq_valid hj hc)
  have hS : IsFormula SourceL S := tr_valid (peq_valid hj ht)
  have hnQ : IsFormula SourceL (neg SourceL Q) := IsSemiformula.neg_iff.mpr hQ
  have hnP : IsFormula SourceL (neg SourceL P) := IsSemiformula.neg_iff.mpr hP
  have hnE : IsFormula SourceL (neg SourceL E) := IsSemiformula.neg_iff.mpr hE
  have hD : IsFormula SourceL D := IsSemiformula.or.mpr ⟨hnE,hS⟩
  let Δ₁ : V := insert (neg SourceL E) (insert Q (∅ : V))
  have hΔ₁ : IsFormulaSet SourceL Δ₁ := fs_cons hnE (fs_cons hQ fs_nil)
  have hQsource : GDerivable T Δ₁ := by
    apply GDerivable.cut_wk hΔ₁ hU (N.uVar c) (nameOfUniq (T := T) hc j) <;> (dsimp [Δ₁,U,Q,E]; set_tac)
  let Δ₂ : V := insert (neg SourceL Q) (insert (neg SourceL P) (insert S (∅ : V)))
  have hΔ₂ : IsFormulaSet SourceL Δ₂ := fs_cons hnQ (fs_cons hnP (fs_cons hS fs_nil))
  have htransfer : GDerivable T Δ₂ := by
    apply GDerivable.cut_wk hΔ₂ hR (nRefl (T := T) t ht)
      (N.atomTransfer (^&c) (^&j) t t hc hj ht ht) <;> (dsimp [Δ₂,Q,R,P,S]; set_tac)
  let Δ₃ : V := insert (neg SourceL E) (insert (neg SourceL P) (insert S (∅ : V)))
  have hΔ₃ : IsFormulaSet SourceL Δ₃ := fs_cons hnE (fs_cons hnP (fs_cons hS fs_nil))
  have hfinal : GDerivable T Δ₃ := by
    apply GDerivable.cut_wk hΔ₃ hQ hQsource htransfer <;> (dsimp [Δ₁,Δ₂,Δ₃,Q,P,E,S]; set_tac)
  have hDder : GDerivable T (insert (neg SourceL P) (insert D (∅ : V))) := by
    apply GDerivable.or_m (p := neg SourceL E) (q := S) (by simp [D])
    apply GDerivable.wk (fs_cons hnE (fs_cons hS (fs_cons hnP (fs_cons hD fs_nil)))) _ hfinal
    dsimp [Δ₃]
    set_tac
  rw [tr_or (IsSemiformula.neg_iff.mpr (peq_valid hj hc)) (peq_valid hj ht), tr_neg (peq_valid hj hc)]
  exact hDder
#print axioms nameOfEq_open
end generic
end PA194GuardedCompiler
