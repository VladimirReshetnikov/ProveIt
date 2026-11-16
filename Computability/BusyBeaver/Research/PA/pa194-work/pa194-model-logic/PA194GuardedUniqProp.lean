import PA194NameUniqSubstSecond
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

theorem guarded_uniq_prop {A B C : V} (hA : IsFormula SourceL A)
    (hB : IsFormula SourceL B) (hC : IsFormula SourceL C) :
    GDerivable T (insert (neg SourceL (neg SourceL A ^⋎ (neg SourceL B ^⋎ C)))
      (insert (neg SourceL B) (insert (neg SourceL A ^⋎ C) (∅ : V)))) := by
  let D : V := neg SourceL A ^⋎ C
  let M : V := neg SourceL (neg SourceL A ^⋎ (neg SourceL B ^⋎ C))
  let Δ : V := insert M (insert (neg SourceL B) (insert D (∅ : V)))
  have hnA : IsFormula SourceL (neg SourceL A) := IsSemiformula.neg_iff.mpr hA
  have hnB : IsFormula SourceL (neg SourceL B) := IsSemiformula.neg_iff.mpr hB
  have hnC : IsFormula SourceL (neg SourceL C) := IsSemiformula.neg_iff.mpr hC
  have hD : IsFormula SourceL D := IsSemiformula.or.mpr ⟨hnA,hC⟩
  have hM : IsFormula SourceL M := IsSemiformula.neg_iff.mpr
    (IsSemiformula.or.mpr ⟨hnA,IsSemiformula.or.mpr ⟨hnB,hC⟩⟩)
  have hΔ : IsFormulaSet SourceL Δ := fs_cons hM (fs_cons hnB (fs_cons hD fs_nil))
  have hleft : GDerivable T (insert A Δ) := by
    apply GDerivable.or_m (p := neg SourceL A) (q := C) (by simp [Δ,D])
    apply GDerivable.em (fs_cons hnA (fs_cons hC (fs_cons hA hΔ))) A <;> simp
  have hmid : GDerivable T (insert B Δ) := by
    apply GDerivable.em (fs_cons hB hΔ) B <;> simp [Δ]
  have hright : GDerivable T (insert (neg SourceL C) Δ) := by
    apply GDerivable.or_m (p := neg SourceL A) (q := C) (by simp [Δ,D])
    apply GDerivable.em (fs_cons hnA (fs_cons hC (fs_cons hnC hΔ))) C <;> simp
  let N : V := B ^⋏ neg SourceL C
  have hN : IsFormula SourceL N := IsSemiformula.and.mpr ⟨hB,hnC⟩
  have hmid' : GDerivable T (insert B (insert N Δ)) := by
    apply GDerivable.wk (fs_cons hB (fs_cons hN hΔ)) _ hmid
    intro x hx
    simp only [mem_bitInsert_iff] at hx ⊢
    tauto
  have hright' : GDerivable T (insert (neg SourceL C) (insert N Δ)) := by
    apply GDerivable.wk (fs_cons hnC (fs_cons hN hΔ)) _ hright
    intro x hx
    simp only [mem_bitInsert_iff] at hx ⊢
    tauto
  have hNder : GDerivable T (insert N Δ) := GDerivable.and_m (by simp [N]) hmid' hright'
  have hMeq : M = A ^⋏ N := by
    dsimp [M,N]
    rw [neg_or hnA.isUFormula (IsSemiformula.or.mpr ⟨hnB,hC⟩).isUFormula,
      neg_or hnB.isUFormula hC.isUFormula,
      IsUFormula.neg_neg hA.isUFormula,IsUFormula.neg_neg hB.isUFormula]
  have hout : GDerivable T Δ := GDerivable.and_m (by simp [Δ,hMeq]) hleft hNder
  exact hout
#print axioms guarded_uniq_prop
end generic
end PA194GuardedCompiler
