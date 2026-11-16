import PA194NameToValue
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194NameValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]

theorem nameToValueGuarded (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (^∃ (valBody s)) (∅ : V))) := by
  have hA : IsFormula SourceL (neg SourceL (tr (exName s))) :=
    IsSemiformula.neg_iff.mpr (tr_valid (exName_valid hs))
  have hB : IsFormula SourceL (^∃ (valBody s)) :=
    IsSemiformula.exs.mpr (by simpa using valBody_valid hs)
  let A : Bootstrapping.Formula V SourceL := ⟨_,hA⟩
  let B : Bootstrapping.Formula V SourceL := ⟨_,hB⟩
  let U : InternalTheory V SourceL := ⟨T,inferInstance⟩
  have h : Derivable T (insert ((A ⋎ B).val) (∅ : V)) := by
    simpa [A,B] using (nameToValue T s hs).toDerivable
  let d : U ⊢!ᵈᵉʳ insert (A ⋎ B) ∅ := Derivable.toTDerivation _ h
  have h' := (TDerivation.orInv d).toDerivable
  refine ⟨0,?_⟩
  simpa [guards_zero,A,B] using h'
#print axioms nameToValueGuarded
end generic
end PA194NameValueSchema
