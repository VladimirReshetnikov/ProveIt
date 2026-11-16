import PA194ForwardFormulaCorrect
import PA194RootFormula
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ForwardTyped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rootParameters_aligned (d : V) : Aligned (rootParameters d)
    (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0)) (.fvar 0) := by
  refine ⟨rootParameters_valid d, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i hi
    have hi' : (i : V) < d+1 := by simpa [rootParameters] using hi
    simp only [rootParameters,parameters_free]
    rw [nth_repeatVec _ _ hi']
    simp [Semiterm.quote_def]
  · simp [rootParameters,Semiterm.quote_def]

theorem root_translate_quote (p : SourceFormula 0) (d : V)
    (hlen : (⌜p⌝ : V) < len (nth (rootParameters d) 1)) :
    translateFormula (rootParameters d) (⌜p⌝ : V) =
      (⌜formula p (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : V) :=
  formula_quote p _ _ _ _ (rootParameters_aligned d) hlen

theorem rootFormula_quote (p : SourceFormula 0) :
    rootFormula (⌜p⌝ : V) =
      (⌜formula p (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : V) :=
  root_translate_quote p (⌜p⌝ : V) (rootParameters_length _)
#print axioms rootParameters_aligned
#print axioms root_translate_quote
#print axioms rootFormula_quote
end generic
end PA194ForwardTyped
