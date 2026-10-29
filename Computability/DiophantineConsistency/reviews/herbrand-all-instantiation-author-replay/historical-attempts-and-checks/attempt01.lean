import DiophantineConsistency.HerbrandParameterizedWitness

/-! Opening universal closures in the first-order derivation calculus. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandAllInstantiation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate
  HerbrandUniversalPreparation HerbrandParameterizedWitness

noncomputable def specializeDerivation (ψ : Semiproposition language 1) (t : SyntacticTerm language)
    (Γ : List (Proposition language)) (d : Derivation ((∀⁰ ψ) :: Γ)) :
    Derivation ((ψ/[t]) :: Γ) := by
  have d₀ : Derivation [∼(ψ/[t]), ψ/[t]] := (Derivation.eta (ψ/[t])).rotate.cast (by simp)
  have d₁ : Derivation [(∼ψ)/[t], ψ/[t]] := by simpa using d₀
  have d₂ : Derivation [∃⁰ ∼ψ, ψ/[t]] := Derivation.exs d₁
  have d₃ : Derivation [∼(∀⁰ ψ), ψ/[t]] := by simpa using d₂
  exact (d.cut d₃).contra (by simp)

end DiophantineConsistency.HerbrandAllInstantiation
