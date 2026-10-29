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

noncomputable def instantiateAll : (n : ℕ) → (χ : Semisentence language n) →
    (w : Fin n → SyntacticTerm language) → (Γ : List (Proposition language)) →
    Derivation ((Rewriting.emb (∀⁰* χ) : Proposition language) :: Γ) →
    Derivation ((Rew.embSubsts w ▹ χ) :: Γ)
  | 0, χ, w, Γ, d => by simpa using d
  | n+1, χ, w, Γ, d => by
    let tail : Fin n → SyntacticTerm language := fun i => w i.succ
    have d₀ : Derivation ((Rew.embSubsts tail ▹ (∀⁰ χ)) :: Γ) :=
      instantiateAll n (∀⁰ χ) tail Γ (by simpa [allClosure_succ] using d)
    have d₁ : Derivation ((∀⁰ (Rew.embSubsts (#0 :> Rew.bShift ∘ tail) ▹ χ)) :: Γ) := by
      simpa [Rew.q_embSubsts] using d₀
    have d₂ := specializeDerivation (Rew.embSubsts (#0 :> Rew.bShift ∘ tail) ▹ χ) (w 0) Γ d₁
    -- Substituting the first instance cancels the temporary binder shift.
    simpa [← TransitiveRewriting.comp_app, Rew.subst_comp_embSubsts, tail] using d₂

end DiophantineConsistency.HerbrandAllInstantiation
