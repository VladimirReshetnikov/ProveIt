import DiophantineConsistency.FoundationHAPeano
import DiophantineConsistency.FoundationHACurrentNoZero2011

/-! # Conditional PA equivalences for the exact current HA sentence

The source PA equivalence remains an explicit premise. Its existing GG
translation is composed with the proved literal current-sentence bridge.
The negative-source corollary targets the negation of the GG-translated
predicate, not a separately asserted representation of consistency.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHACurrentTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax FoundationHACurrentNoZero2011

/-- The reverse direction of the existing Foundation implication equivalence.
The finite HA assumptions and arithmetic-axiom support are retained. -/
theorem translated_imp_elim {G : List Formula} (φ ψ : Proposition ℒₒᵣ)
    (h : Relative Formula.Ax_s G (formula (φ 🡒 ψ)ᴺ)) :
    Relative Formula.Ax_s G (.imp (formula φᴺ) (formula ψᴺ)) := by
  exact FoundationHAInduction.translated_imp_elim φ ψ h

theorem sentence_imp_elim {φ ψ : ArithmeticSentence}
    (h : Proves (sentence (φ 🡒 ψ)ᴺ)) :
    Proves (.imp (sentence φᴺ) (sentence ψᴺ)) := by
  simp only [sentence, Semiformula.emb_doubleNegation,
    LogicalConnective.HomClass.map_imply] at h ⊢
  exact translated_imp_elim (Rewriting.emb φ) (Rewriting.emb ψ) h

/-- No proof of the source equivalence is supplied by this theorem.
No target stability, model semantics, or axiom-image premise is needed. -/
theorem current_iff_translated {χ : ArithmeticSentence}
    (h : Peano ⊢ classicalSentence 🡘 χ) :
    Proves (.and
      (.imp ArithmeticCurrentEquation2011.unsolvabilitySentence (sentence χᴺ))
      (.imp (sentence χᴺ) ArithmeticCurrentEquation2011.unsolvabilitySentence)) := by
  have hp := FoundationHAPeano.peano_provable h
  change Proves (.and (sentence (classicalSentence 🡒 χ)ᴺ)
    (sentence (χ 🡒 classicalSentence)ᴺ)) at hp
  exact (current_to_source.imp_trans (sentence_imp_elim hp.and_left)).and_intro
    ((sentence_imp_elim hp.and_right).imp_trans source_to_current)

/-- Actual source negation commutes with GG up to a proved intuitionistic
equivalence. This reuses Foundation's existing derivation, not a new recursion. -/
theorem translated_neg (ρ : ArithmeticSentence) :
    Proves (.and
      (.imp (neg (sentence ρᴺ)) (sentence (∼ρ)ᴺ))
      (.imp (sentence (∼ρ)ᴺ) (neg (sentence ρᴺ)))) := by
  obtain ⟨p⟩ := (LO.FirstOrder.Derivation.neg_doubleNegation
    (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)) (Rewriting.emb ρ))
  have hp := FoundationPAHFLogic.intuitionistic_proof p
  change Derives [] (.and
    (.imp (neg (formula (Rewriting.emb ρ)ᴺ)) (formula (∼Rewriting.emb ρ)ᴺ))
    (.imp (formula (∼Rewriting.emb ρ)ᴺ) (neg (formula (Rewriting.emb ρ)ᴺ)))) at hp
  simp only [sentence, Semiformula.emb_doubleNegation,
    LogicalConnective.HomClass.map_neg]
  exact relative_of_derives hp

/-- The resulting target is explicitly `not GG(ρ)`. Identifying ρ with
a chosen refutation predicate and proving the PA premise remain separate. -/
theorem current_iff_neg_translated {ρ : ArithmeticSentence}
    (h : Peano ⊢ classicalSentence 🡘 ∼ρ) :
    Proves (.and
      (.imp ArithmeticCurrentEquation2011.unsolvabilitySentence (neg (sentence ρᴺ)))
      (.imp (neg (sentence ρᴺ)) ArithmeticCurrentEquation2011.unsolvabilitySentence)) := by
  have hp := current_iff_translated h
  have hn := translated_neg ρ
  exact (hp.and_left.imp_trans hn.and_right).and_intro
    (hn.and_left.imp_trans hp.and_right)

end DiophantineConsistency.FoundationHACurrentTransfer
