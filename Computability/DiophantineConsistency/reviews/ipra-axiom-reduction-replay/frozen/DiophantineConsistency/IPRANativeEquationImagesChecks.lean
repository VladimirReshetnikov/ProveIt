import DiophantineConsistency.IPRANativeEquationImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeEquationImages
#check allClosure_dni
#check equality_image
#check definingEquation_image
#print axioms allClosure_dni
#print axioms definingEquation_image
example (n : ℕ) : nativeTheory ⊢ (zeroEquation n)ᴺ :=
  definingEquation_image (DefiningEquation.zero n)
example {n : ℕ} (i : Fin n) : nativeTheory ⊢ (projectionEquation i)ᴺ :=
  definingEquation_image (DefiningEquation.projection i)
example {n : ℕ} (f : Code n) (g : Code (n+2)) :
    nativeTheory ⊢ (recursionBaseEquation f g)ᴺ :=
  definingEquation_image (DefiningEquation.recursionBase f g)
example {n : ℕ} (f : Code n) (g : Codes (n+2) n) :
    nativeTheory ⊢ (compositionEquation f g)ᴺ :=
  definingEquation_image (DefiningEquation.composition f g)
example {n : ℕ} (f : Code n) (g : Code (n+2)) :
    nativeTheory ⊢ (recursionStepEquation f g)ᴺ :=
  definingEquation_image (DefiningEquation.recursionStep f g)
