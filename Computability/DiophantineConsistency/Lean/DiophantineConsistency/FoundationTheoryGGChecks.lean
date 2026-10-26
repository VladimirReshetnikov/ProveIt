import DiophantineConsistency.FoundationTheoryGG

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.FoundationTheoryGGChecks

open LO LO.FirstOrder LO.Entailment
open DiophantineConsistency.FoundationTheoryGG

universe u
variable {L : Language.{u}} [L.DecidableEq]

theorem translated_axiom {T : Theory L} {φ : Sentence L} (h : φ ∈ T) :
    T.ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L) ⊢ φᴺ :=
  theory_intuitionistic (Entailment.by_axm h)

theorem two_axioms (φ ψ : Sentence L) :
    ({φ, ψ} : Theory L).ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L) ⊢ (φ ⋏ ψ)ᴺ := by
  apply theory_intuitionistic
  exact K!_intro (Entailment.by_axm (by simp)) (Entailment.by_axm (by simp))

/-- Duplicate assumptions remain an actual finite list; no cardinality
or set-injectivity premise is imposed on the source proof. -/
def duplicate_axioms (φ : Sentence L) :
    (Sequent.embed [φ, φ])ᴺ ⊢[𝗜𝗻𝘁¹]! (φ : Proposition L)ᴺ :=
  finiteProof <| (Derivation.eta (φ : Proposition L)).contraction (by
    simp [Sequent.embed])

omit [L.DecidableEq] in
theorem translated_empty :
    ((∅ : Theory L).ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L)).theory = ∅ := by
  simp [Theory.ToTheoryᵢ]

theorem empty_theory {φ : Sentence L} (h : (∅ : Theory L) ⊢ φ) :
    (∅ : Theory L).ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L) ⊢ φᴺ :=
  theory_intuitionistic h

/-- This proves the negative translation of excluded middle, not
unrestricted excluded middle in the intuitionistic target. -/
theorem excluded_middle_translated (φ : Sentence L) :
    (∅ : Theory L).ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L) ⊢ (φ ⋎ ∼φ)ᴺ := by
  apply theory_intuitionistic
  apply Theory.Proof.of_LK_provable
  refine ⟨?_⟩
  change ⊢ᴸᴷ¹ [(Rewriting.emb (φ ⋎ ∼φ) : Proposition L)]
  simpa using (Derivation.eta (φ : Proposition L)).or

theorem proof_context_retained {T : Theory L} {φ : Sentence L}
    (p : T ⊢! φ) :
    (theoryProof (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ L)) p).ctx =
      (Sequent.embed p.axioms)ᴺ := rfl

theorem proof_context_length {T : Theory L} {φ : Sentence L}
    (p : T ⊢! φ) :
    (theoryProof (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ L)) p).ctx.length =
      p.axioms.length := by
  rw [proof_context_retained]
  simp [Sequent.doubleNegation, Sequent.embed]

-- The generic adapter even supports the minimal logical target; it does
-- not introduce a hidden excluded-middle or arithmetic-axiom premise.
example {T : Theory L} {φ : Sentence L} (h : T ⊢ φ) :
    T.ToTheoryᵢ (𝗠𝗶𝗻¹ : Hilbertᵢ L) ⊢ φᴺ :=
  theory_godelGentzen h

#print axioms DiophantineConsistency.FoundationTheoryGG.finiteProof
#print axioms DiophantineConsistency.FoundationTheoryGG.theoryProof
#print axioms DiophantineConsistency.FoundationTheoryGG.theory_godelGentzen
#print axioms DiophantineConsistency.FoundationTheoryGG.theory_intuitionistic
#print axioms translated_axiom
#print axioms two_axioms
#print axioms excluded_middle_translated
#print axioms proof_context_length

end DiophantineConsistency.FoundationTheoryGGChecks
