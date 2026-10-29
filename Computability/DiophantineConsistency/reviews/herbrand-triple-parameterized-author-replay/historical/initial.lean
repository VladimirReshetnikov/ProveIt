import DiophantineConsistency.HerbrandTripleExtraction
import DiophantineConsistency.HerbrandAllInstantiation
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandTripleParameterized
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAUniversalCandidate HerbrandUniversalPreparation HerbrandTripleExtraction
  HerbrandAllInstantiation HerbrandExistentialSequents

def parameterTripleMatrix {n : ℕ} (φ : Semisentence language (n+3)) : Semiproposition language 3 :=
  (((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))).q).q).q ▹ φ

noncomputable def prepareAllTriple {n : ℕ} (φ : Semisentence language (n+3)) (hOpen : φ.Open)
    (p : Theory.Proof UniversalAxiom (∀⁰* ∃⁰ ∃⁰ ∃⁰ φ)) :
    Prepared (∃⁰ ∃⁰ (parameterTripleMatrix φ)) p.axioms := by
  have hopen : (parameterTripleMatrix φ).Open := by
    change (parameterTripleMatrix φ).qr = 0
    unfold parameterTripleMatrix
    rw [PRAFormulaParameters.qr_rew]
    exact hOpen
  apply prepareTriple (parameterTripleMatrix φ) hopen p.axioms p.axioms_mem
  have d := p.derivation
  change Derivation (((∀⁰* ∃⁰ ∃⁰ ∃⁰ φ) :: ∼p.axioms).map Rewriting.emb) at d
  have d₀ : Derivation ((Rewriting.emb (∀⁰* ∃⁰ ∃⁰ ∃⁰ φ) : Proposition language) :: ∼Sequent.embed p.axioms) := by
    simpa [Sequent.embed] using d
  have d₁ := instantiateAll n (∃⁰ ∃⁰ ∃⁰ φ) (fun i : Fin n => .fvar i.val) (∼Sequent.embed p.axioms) d₀
  simpa [parameterTripleMatrix, Rew.q_embSubsts, Function.comp_def] using d₁

theorem universal_proves_parameterTripleDisjunction {n : ℕ} (φ : Semisentence language (n+3)) (hOpen : φ.Open)
    (p : Theory.Proof UniversalAxiom (∀⁰* ∃⁰ ∃⁰ ∃⁰ φ)) :
    UniversalAxiom ⊢ (tripleDisjunction (parameterTripleMatrix φ)
      (existentialTerms (prepareAllTriple φ hOpen p).derivation)).univCl := by
  have hopen : (parameterTripleMatrix φ).Open := by
    change (parameterTripleMatrix φ).qr = 0
    unfold parameterTripleMatrix
    rw [PRAFormulaParameters.qr_rew]
    exact hOpen
  exact universal_proves_preparedTripleDisjunction (parameterTripleMatrix φ) hopen p.axioms p.axioms_mem (prepareAllTriple φ hOpen p)
end DiophantineConsistency.HerbrandTripleParameterized
