import DiophantineConsistency.PRASubSuccSelfNonzero
import DiophantineConsistency.IPRAFullGGTransfer
set_option autoImplicit false
namespace DiophantineConsistency.IPRASubSuccSelfNonzero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRASubSuccSelfNonzero IPRANativeTheory

def result : Sentenceᵢ language := ∀⁰ ∼(Semiformulaᵢ.rel .eq ![term,zero])
theorem native : nativeTheory ⊢ result := by
  have h := IPRAFullGGTransfer.from_classical proved
  simpa [sentence, result, Semiformula.doubleNegation] using h

end DiophantineConsistency.IPRASubSuccSelfNonzero
