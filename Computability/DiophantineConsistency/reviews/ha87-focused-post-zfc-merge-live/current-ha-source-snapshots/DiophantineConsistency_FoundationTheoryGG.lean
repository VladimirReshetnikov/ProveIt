import Foundation.FirstOrder.NegationTranslation.GoedelGentzen

set_option autoImplicit false
set_option Elab.async false

/-!
Finite-theory lifting of Foundation's existing Goedel--Gentzen algorithm.
This targets the image of the given axioms under negative translation.
It does not identify that image with conventional Heyting arithmetic.
-/
namespace DiophantineConsistency.FoundationTheoryGG

open LO LO.FirstOrder LO.Entailment

universe u
variable {L : Language.{u}} [L.DecidableEq] {Λ : Hilbertᵢ L}

/-- A classical proof from a finite list gives an intuitionistic proof from
the same list after translation. The existing recursive GG map is reused. -/
def finiteProof {φ : Sentence L} {Γ : List (Sentence L)}
    (d : ⊢ᴸᴷ¹ ((φ : Proposition L) :: ∼Sequent.embed Γ)) :
    (Sequent.embed Γ)ᴺ ⊢[Λ]! (φ : Proposition L)ᴺ := by
  have hbot : ((∼(φ : Proposition L))ᴺ :: (Sequent.embed Γ)ᴺ) ⊢[Λ]! ⊥ := by
    simpa using (Derivation.gödelGentzen (Λ := Λ) d)
  have hn : (Sequent.embed Γ)ᴺ ⊢[Λ]! ∼(∼(φ : Proposition L))ᴺ :=
    FiniteContext.deduct hbot
  have he : Λ ⊢! ∼(∼(φ : Proposition L))ᴺ 🡒 (φ : Proposition L)ᴺ := by
    simpa using K_left (Derivation.negDoubleNegation (Λ := Λ) (∼(φ : Proposition L)))
  exact FiniteContext.of he ⨀ hn

/-- Actual proof-tree adapter; the finite arithmetic/theory axioms remain
explicitly present in the target theory. No semantic completeness is used. -/
def theoryProof {T : Theory L} {φ : Sentence L} (p : T ⊢! φ) :
    T.ToTheoryᵢ Λ ⊢! φᴺ := by
  change (Rewriting.emb '' (T.ToTheoryᵢ Λ).theory) *⊢[Λ]!
    (Rewriting.emb φᴺ : Propositionᵢ L)
  refine ⟨(Sequent.embed p.axioms)ᴺ, ?_, ?_⟩
  · intro ψ hψ
    simp only [Sequent.doubleNegation, Sequent.embed, List.mem_map] at hψ
    rcases hψ with ⟨χ, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨aᴺ, ?_, ?_⟩
    · exact ⟨a, p.axioms_mem a ha, rfl⟩
    · exact Semiformula.emb_doubleNegation a
  · have d : ⊢ᴸᴷ¹ ((φ : Proposition L) :: ∼Sequent.embed p.axioms) := by
      simpa [OneSidedLK.Pullback, Sequent.embed] using p.derivation
    simpa only [Semiformula.emb_doubleNegation] using
      (finiteProof (Λ := Λ) d)

/-- Existence of a classical theory proof implies existence of an
intuitionistic proof over the translated axioms. -/
theorem theory_godelGentzen {T : Theory L} {φ : Sentence L}
    (h : T ⊢ φ) : T.ToTheoryᵢ Λ ⊢ φᴺ := by
  rcases h with ⟨p⟩
  exact ⟨theoryProof p⟩

/-- The explicit intuitionistic (ex-falso, no unrestricted LEM) target. -/
theorem theory_intuitionistic {T : Theory L} {φ : Sentence L}
    (h : T ⊢ φ) : T.ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L) ⊢ φᴺ :=
  theory_godelGentzen h

end DiophantineConsistency.FoundationTheoryGG
