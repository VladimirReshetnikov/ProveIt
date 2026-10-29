import DiophantineConsistency.HerbrandExistentialSequents
import DiophantineConsistency.PRAUniversalAxiomSyntax
import Foundation.FirstOrder.Hauptsatz

/-! Cut-free preparation for an existential sequent over universal candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandUniversalPreparation
open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRAUniversalCandidate DiophantineConsistency.PRAUniversalSyntax
  DiophantineConsistency.PRAUniversalAxiomSyntax DiophantineConsistency.HerbrandExistentialSequents

instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem negatedAxiom_noUniversal (σ : Sentence language) (hσ : UniversalAxiom σ) :
    NoUniversal (∼(Rewriting.emb σ : Proposition language)) := by
  have hu := universalAxiom_isUniversal hσ
  have he := (universalPrefix_rew_iff σ (Rew.emb : Rew language Empty 0 ℕ 0)).mpr hu
  exact noUniversal_neg_of_prefix _ he

theorem existentialSequent_noUniversal (φ : Semiproposition language 1) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ) :
    ∀ ψ ∈ (∃⁰ φ) :: ∼Sequent.embed axioms, NoUniversal ψ := by
  intro ψ hψ
  simp only [List.mem_cons] at hψ
  rcases hψ with rfl | hψ
  · exact noUniversal_of_open φ hOpen
  · simp only [List.tilde_def, Sequent.embed, List.mem_map] at hψ
    obtain ⟨χ, hχ, hψ⟩ := hψ
    obtain ⟨σ, hσ, rfl⟩ := hχ
    subst ψ
    exact negatedAxiom_noUniversal σ (hAxioms σ hσ)

/-- A cut-free proof for an existential goal with the precise finite list of
universal axioms preserved. It has no universal-rule nodes. -/
structure Prepared (φ : Semiproposition language 1) (axioms : List (Sentence language)) where
  derivation : Derivation ((∃⁰ φ) :: ∼Sequent.embed axioms)
  cutFree : derivation.IsCutFree
  noAll : NoAllRule derivation

/-- Eliminate cuts and certify the existential-only derivation shape. -/
noncomputable def prepare (φ : Semiproposition language 1) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (d : Derivation ((∃⁰ φ) :: ∼Sequent.embed axioms)) : Prepared φ axioms := by
  let dd := Derivation.Canonical.hauptsatz d
  exact ⟨dd.val, dd.property,
    cutFree_noUniversalRule dd.val dd.property (existentialSequent_noUniversal φ hOpen axioms hAxioms)⟩

end DiophantineConsistency.HerbrandUniversalPreparation
