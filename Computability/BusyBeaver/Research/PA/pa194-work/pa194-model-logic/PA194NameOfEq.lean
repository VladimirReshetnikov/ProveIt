import PA194NameOfEqOpen
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

theorem nameOfEq (N : NameOfEqPrereqs (V := V) T) {t : V}
    (ht : IsSemiterm PA194PAeq.language 0 t) (c : V) :
    GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (tr (nameAll (^&c) t)) (∅ : V))) := by
  have hc : IsSemiterm PA194PAeq.language 0 (^&c) := by simp
  let p : V := neg PA194PAeq.language (peq (^#(0 : V)) (termBShift PA194PAeq.language (^&c))) ^⋎
      peq (^#(0 : V)) (termBShift PA194PAeq.language t)
  have hp0 := peq_valid (by simp : IsSemiterm PA194PAeq.language 1 (^#(0 : V))) (bShift_valid hc)
  have hp1 := peq_valid (by simp : IsSemiterm PA194PAeq.language 1 (^#(0 : V))) (bShift_valid ht)
  have hp : IsSemiformula PA194PAeq.language 1 p :=
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hp0,hp1⟩
  have hfree : free PA194PAeq.language p =
      neg PA194PAeq.language (peq (^&(0 : V)) (^&(c+1))) ^⋎
        peq (^&(0 : V)) (termShift PA194PAeq.language t) := by
    dsimp [p]
    rw [free_orA (IsSemiformula.neg_iff.mpr hp0) hp1, free_negA hp0,
      free_peq_bvar hc, free_peq_bvar ht, termShift_fvar]
  have e : shift SourceL (neg SourceL (tr (peq (^&c) t))) =
      neg SourceL (tr (peq (^&(c+1)) (termShift PA194PAeq.language t))) := by
    rw [shift_neg_tr (peq_valid hc ht),shift_peq hc ht,termShift_fvar]
  let E : V := neg SourceL (tr (peq (^&c) t))
  let F : V := tr (^∀ p)
  let Δ : V := insert F (insert E (∅ : V))
  have hE : IsFormula SourceL E := IsSemiformula.neg_iff.mpr (tr_valid (peq_valid hc ht))
  have hF : IsFormula SourceL F := tr_valid (IsSemiformula.all.mpr (by simpa using hp))
  have hΔ : IsFormulaSet SourceL Δ := fs_cons hF (fs_cons hE fs_nil)
  have hopen := nameOfEq_open N ht.termShift (c+1) (0 : V)
  have hpre : GDerivable T (insert (free SourceL (trBody p)) (setShift SourceL Δ)) := by
    apply GDerivable.wk (fs_cons (trBody_valid hp).free hΔ.setShift) _ hopen
    rw [←tr_free hp,hfree]
    dsimp [Δ,E]
    rw [mem_setShift_insert,mem_setShift_insert,setShift_empty,e]
    intro x hx
    simp only [mem_bitInsert_iff] at hx ⊢
    tauto
  have hout : GDerivable T Δ := GDerivable.all_rel (trBody_valid hp) (by simp [Δ,F,←tr_all hp]) hpre
  apply GDerivable.wk (fs_cons hE (fs_cons (tr_valid (nameAll_valid hc ht)) fs_nil)) _ hout
  dsimp [Δ,F,p,nameAll]
  intro x hx
  simp only [mem_bitInsert_iff] at hx ⊢
  tauto
#print axioms nameOfEq
end generic
end PA194GuardedCompiler
