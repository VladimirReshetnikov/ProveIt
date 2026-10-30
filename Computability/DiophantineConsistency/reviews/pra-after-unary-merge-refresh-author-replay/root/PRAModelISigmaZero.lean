import DiophantineConsistency.ParsonsISigmaZeroComparison
import Foundation.FirstOrder.Arithmetic.IOpen.Basic
set_option autoImplicit false
namespace DiophantineConsistency.PRAModelISigmaZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory ParsonsISigmaZeroComparison

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Structure.Eq language M] in
/-- The first-order arithmetic reduct of every candidate-PRA model satisfies
Foundation's IΣ₀ theory. -/
theorem modelReductISigmaZero :
    letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
    M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  constructor
  intro σ hσ
  have hp : 𝗜𝚺₀ ⊢ σ := ⟨Entailment.Axiomatized.byAxm hσ⟩
  have hmap := comparison hp
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hmap
  exact Semiformula.models_lMap.mp hm

omit [Structure.Eq language M] in
/-- In particular, the arithmetic reduct satisfies Foundation's IOpen. -/
theorem modelReductIOpen :
    letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
    M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := by
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  exact models_of_subtheory (U := 𝗜𝚺₀) modelReductISigmaZero
end models
end DiophantineConsistency.PRAModelISigmaZero
