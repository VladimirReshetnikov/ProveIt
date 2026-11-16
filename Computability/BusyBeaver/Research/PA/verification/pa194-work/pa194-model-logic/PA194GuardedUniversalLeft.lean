import PA194GuardedUniversalIntro
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

/-- Eliminate a translated universal at a free variable in guarded one-sided form. -/
theorem guarded_tr_all_left {p Δ : V} (hp : IsSemiformula PA194PAeq.language 1 p) (j : V)
    (h : GDerivable T (insert (neg SourceL (tr (substs1 PA194PAeq.language (^&j) p))) Δ)) :
    GDerivable T (insert (neg SourceL (tr (^∀ p))) Δ) := by
  let a : V := neg SourceL (tr (^∀ p))
  let b : V := neg SourceL (tr (substs1 PA194PAeq.language (^&j) p))
  have hpj : IsSemiformula PA194PAeq.language 0 (substs1 PA194PAeq.language (^&j) p) :=
    IsSemiformula.substs1 (by simp) hp
  have ha : IsFormula SourceL a := IsSemiformula.neg_iff.mpr (tr_valid (IsSemiformula.all.mpr (by simpa using hp)))
  have hb : IsFormula SourceL b := IsSemiformula.neg_iff.mpr (tr_valid hpj)
  have hΔ : IsFormulaSet SourceL Δ := (IsFormulaSet.insert_iff.mp h.isFormulaSet).2
  have hs : IsFormulaSet SourceL (insert b (insert a Δ)) := fs_cons hb (fs_cons ha hΔ)
  have hw : GDerivable T (insert b (insert a Δ)) := by
    apply GDerivable.wk hs _ h
    intro x hx
    simp only [mem_bitInsert_iff] at hx ⊢
    tauto
  have hn : IsSemiformula SourceL 1 (neg SourceL (trBody p)) :=
    IsSemiformula.neg_iff.mpr (trBody_valid hp)
  have hm : ^∃ (domainCode (^#(0 : V)) ^⋏ neg SourceL (trBody p)) ∈ insert a Δ := by
    apply mem_bitInsert_iff.mpr
    left
    dsimp [a]
    rw [tr_all hp, neg_all_rel (trBody_valid hp)]
  have hpre : GDerivable T (insert (substs1 SourceL (^&j) (neg SourceL (trBody p))) (insert a Δ)) := by
    rw [substs1_negS (trBody_valid hp) (by simp), ←tr_substs1_fvar hp j]
    exact hw
  exact GDerivable.ex_rel hn hm j hpre
#print axioms guarded_tr_all_left
end generic
end PA194GuardedCompiler
