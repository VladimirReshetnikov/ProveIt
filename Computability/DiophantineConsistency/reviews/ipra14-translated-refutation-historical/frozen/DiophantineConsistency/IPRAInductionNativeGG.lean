import DiophantineConsistency.IPRAInductionAxiomGG
import DiophantineConsistency.IPRANativeTheory
/-! Native iPRA proves the GG translation of each actual classical open
induction axiom. Other classical PRA axiom images are separate obligations. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAInductionNativeGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory

theorem induction_scheme_gg (σ : Sentence language)
    (hσ : σ ∈ InductionScheme language Semiformula.Open) :
    IPRANativeTheory.nativeTheory ⊢ σᴺ := by
  apply IPRABodyBinding.induction_scheme_gg_in_theory IPRANativeTheory.nativeTheory
  · intro τ hτ
    exact IPRANativeTheory.NativeAxiom.induction hτ
  · exact hσ
end DiophantineConsistency.IPRAInductionNativeGG
