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

/-- A closed existential theorem provides the exact finite universal-axiom
sequent required by `prepare`. -/
noncomputable def prepareClosed (φ : Semisentence language 1) (hOpen : φ.Open)
    (p : Theory.Proof UniversalAxiom (∃⁰ φ)) : Prepared (Rewriting.emb φ) p.axioms := by
  have hqr : ∀ {n : ℕ} (ψ : Semisentence language n),
      (Rewriting.emb ψ : Semiproposition language n).qr = ψ.qr := by
    intro n ψ
    induction ψ using Semiformula.rec' <;> simp [*, Semiformula.qr]
  have hopen' : (Rewriting.emb φ : Semiproposition language 1).Open := by
    change (Rewriting.emb φ : Semiproposition language 1).qr = 0
    rw [hqr]
    exact hOpen
  apply prepare (Rewriting.emb φ) hopen' p.axioms p.axioms_mem
  have d := p.derivation
  change Derivation (((∃⁰ φ) :: ∼p.axioms).map Rewriting.emb) at d
  simpa [Sequent.embed] using d

end DiophantineConsistency.HerbrandUniversalPreparation
