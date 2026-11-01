import DiophantineConsistency.IPRAFunctionCongruenceClosed
import DiophantineConsistency.IPRAFiniteConjGG
/-! The actual Foundation arbitrary-arity function congruence GG image. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAFunctionCongruenceGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory

theorem funcExt_image {k : ℕ} (f : language.Func k) :
    nativeTheory ⊢ (Theory.Eq.funcExt f)ᴺ := by
  have h := IPRAFunctionCongruenceClosed.function_native f
  change nativeTheory ⊢ IPRAFiniteConjGG.functionCongruenceI f at h
  exact Entailment.mdp! (IPRAFiniteConjGG.functionCongruence_adapter f) h
end DiophantineConsistency.IPRAFunctionCongruenceGG
