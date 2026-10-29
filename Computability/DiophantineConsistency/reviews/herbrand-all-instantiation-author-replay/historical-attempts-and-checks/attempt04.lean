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
    have hv : (Rew.subst ![w 0] ∘ (#0 :> Rew.bShift ∘ tail)) = w := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [tail]
    simpa [← TransitiveRewriting.comp_app, Rew.subst_comp_embSubsts, hv] using d₂

/-- A proof of the closed universal-existential statement yields a prepared
existential sequent with the original finite universal-axiom list. -/
noncomputable def prepareAllExists {n : ℕ} (φ : Semisentence language (n+1)) (hOpen : φ.Open)
    (p : Theory.Proof UniversalAxiom (∀⁰* ∃⁰ φ)) : Prepared (parameterMatrix φ) p.axioms := by
  have hopen : (parameterMatrix φ).Open := by
    change (parameterMatrix φ).qr = 0
    unfold parameterMatrix
    rw [PRAFormulaParameters.qr_rew]
    exact hOpen
  apply prepare (parameterMatrix φ) hopen p.axioms p.axioms_mem
  have d := p.derivation
  change Derivation (((∀⁰* ∃⁰ φ) :: ∼p.axioms).map Rewriting.emb) at d
  have d₀ : Derivation ((Rewriting.emb (∀⁰* ∃⁰ φ) : Proposition language) :: ∼Sequent.embed p.axioms) := by
    simpa [Sequent.embed] using d
  have d₁ := instantiateAll n (∃⁰ φ) (fun i : Fin n => .fvar i.val) (∼Sequent.embed p.axioms) d₀
  simpa [parameterMatrix, Rew.q_embSubsts, Function.comp_def] using d₁

/-- Witness extraction for a theorem of the universal candidate presentation. -/
theorem PRA_witness_of_universal_exists {n : ℕ} (φ : Semisentence language (n+1)) (hOpen : φ.Open)
    (h : UniversalAxiom ⊢ (∀⁰* ∃⁰ φ)) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* PRAHerbrandSelection.openMatrixAt φ c) := by
  obtain ⟨p⟩ := h
  exact PRA_parameterizedPreparedWitness φ hOpen p.axioms p.axioms_mem (prepareAllExists φ hOpen p)

end DiophantineConsistency.HerbrandAllInstantiation
