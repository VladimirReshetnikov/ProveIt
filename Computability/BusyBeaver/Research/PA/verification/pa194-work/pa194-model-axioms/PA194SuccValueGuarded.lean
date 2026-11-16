import PA194SuccValueImplication
import PA194SuccTotalQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SuccValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher PA194DomainSuccessorClosedTemplate
open M6.PA.RelationalSource
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]

theorem succTotalCode_valid : IsFormula SourceL (succTotalCode : V) := by
  rw [←succTotalCode_quote]
  exact Semiformula.quote_isSemiformula₀ (∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)

theorem succValueGuarded (hTotal : Provable T (succTotalCode : V)) (s : V)
    (hs : IsSemiterm PA194PAeq.language 0 s) :
    GDerivable T (insert (neg SourceL (^∃ (valBody s))) (insert (^∃ (valBody (succT s))) (∅ : V))) := by
  have hA : IsFormula SourceL (succTotalCode : V) := succTotalCode_valid
  have hB : IsFormula SourceL (^∃ (valBody s)) := IsSemiformula.exs.mpr (by simpa using valBody_valid hs)
  have hC : IsFormula SourceL (^∃ (valBody (succT s))) :=
    IsSemiformula.exs.mpr (by simpa using valBody_valid (succT_valid hs))
  let A : Bootstrapping.Formula V SourceL := ⟨_,hA⟩
  let B : Bootstrapping.Formula V SourceL := ⟨_,hB⟩
  let C : Bootstrapping.Formula V SourceL := ⟨_,hC⟩
  let U : InternalTheory V SourceL := ⟨T,inferInstance⟩
  have h : Derivable T (insert ((∼A ⋎ (∼B ⋎ C)).val) (∅ : V)) := by
    simpa [A,B,C] using (succValueImplication T s hs).toDerivable
  let d : U ⊢!ᵈᵉʳ insert (∼A ⋎ (∼B ⋎ C)) ∅ := Derivable.toTDerivation _ h
  let d1 := TDerivation.orInv d
  let d2 := TDerivation.orInv (TDerivation.rotate₁ d1)
  have hseq : GDerivable T (insert (neg SourceL (^∃ (valBody s)))
      (insert (^∃ (valBody (succT s))) (insert (neg SourceL succTotalCode) (∅ : V)))) := by
    refine ⟨0,?_⟩
    simpa [guards_zero,A,B,C] using d2.toDerivable
  have ht : GDerivable T (insert succTotalCode (∅ : V)) := by
    refine ⟨0,?_⟩
    simpa [guards_zero] using hTotal.toDerivable
  have hnB : IsFormula SourceL (neg SourceL (^∃ (valBody s))) := IsSemiformula.neg_iff.mpr hB
  have hΔ : IsFormulaSet SourceL (insert (neg SourceL (^∃ (valBody s)))
      (insert (^∃ (valBody (succT s))) (∅ : V))) := fs_cons hnB (fs_cons hC fs_nil)
  apply GDerivable.cut_wk hΔ hA ht hseq <;> set_tac
#print axioms succTotalCode_valid
#print axioms succValueGuarded
end generic
end PA194SuccValueSchema
