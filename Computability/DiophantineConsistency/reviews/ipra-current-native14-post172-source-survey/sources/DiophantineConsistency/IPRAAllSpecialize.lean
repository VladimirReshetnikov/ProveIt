import DiophantineConsistency.IPRANativeBasicImages
/-! Uniform intuitionistic specialization of a finite universal closure,
including the actual native Leibniz substitution schema. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAAllSpecialize
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
variable {L : Language} {Λ : Hilbertᵢ L}

theorem subst_after_q {n : ℕ} (p : Semiformulaᵢ L ℕ (n+1))
    (v : Fin (n+1) → SyntacticTerm L) :
    (((Rew.subst (fun i => v i.succ)).q ▹ p)/[v 0]) = p ⇜ v := by
  simp only [Rewriting.subst, ← TransitiveRewriting.comp_app]
  congr 2
  ext i
  · cases i using Fin.cases <;> simp [Rew.comp_app]
  · simp [Rew.comp_app]

theorem allClosure_specialize : ∀ n (p : Semiformulaᵢ L ℕ n)
    (v : Fin n → SyntacticTerm L), Λ ⊢ (∀⁰* p) 🡒 (p ⇜ v)
  | 0, p, v => by
    have : (p ⇜ v) = p := by simp [Rewriting.subst]
    rw [this]; exact ⟨Entailment.C_id⟩
  | n+1, p, v => by
    have ih := allClosure_specialize n (∀⁰ p) (fun i => v i.succ)
    have hspec : Λ ⊢ ((∀⁰ p) ⇜ (fun i => v i.succ)) 🡒 (p ⇜ v) := by
      have h := HilbertProofᵢ.all₁ (Λ := Λ) ((Rew.subst (fun i => v i.succ)).q ▹ p) (v 0)
      apply Nonempty.intro
      apply Entailment.cast h ?_
      simp only [subst_after_q, Rewriting.subst, Rewriting.app_all]
    simpa only [allClosure_succ] using Entailment.C!_trans ih hspec
theorem specialize_over_context {n : ℕ} (p : Semiformulaᵢ L ℕ n)
    (v : Fin n → SyntacticTerm L) (Γ : List (Propositionᵢ L))
    (h : Γ ⊢[Λ] ∀⁰* p) : Γ ⊢[Λ] p ⇜ v := by
  obtain ⟨h⟩ := h
  obtain ⟨hs⟩ := allClosure_specialize n p v
  exact ⟨(Entailment.FiniteContext.of hs) ⨀ h⟩
open PRALanguage PRATheory IPRANativeTheory

def leibnizBody {n : ℕ} (p : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+2) :=
    (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#1]) 🡒 (eqLeft p 🡒 eqRight p)

theorem specialize_native_leibniz {n : ℕ} (p : Semisentenceᵢ language (n+1))
    (v : Fin (n+2) → SyntacticTerm language) (Γ : List (Propositionᵢ language))
    (h : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ language)] Rewriting.emb (eqSubstitutionI p)) :
    Γ ⊢[𝗜𝗻𝘁¹] (Rewriting.emb (leibnizBody p) : Semiformulaᵢ language ℕ (n+2)) ⇜ v := by
  apply specialize_over_context _ v Γ
  simpa only [eqSubstitutionI, leibnizBody, Rewriting.emb_allClosure] using h
end DiophantineConsistency.IPRAAllSpecialize
