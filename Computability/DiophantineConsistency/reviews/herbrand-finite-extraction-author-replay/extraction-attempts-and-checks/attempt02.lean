import DiophantineConsistency.HerbrandUniversalPreparation
import DiophantineConsistency.HerbrandBoundedSoundness
import DiophantineConsistency.HerbrandBoundedTruth

/-! Extract a finite witness disjunction from an existential sequent. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandFiniteExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAFormulaParameters PRAUniversalCandidate
  PRAUniversalEquivalence HerbrandExistentialSequents HerbrandUniversalPreparation
  HerbrandBoundedSemantics HerbrandBoundedSoundness HerbrandBoundedTruth

def termDisjunction (φ : Semiproposition language 1) : List (SyntacticTerm language) → Proposition language
  | [] => ⊥
  | t :: ts => φ/[t] ⋎ termDisjunction φ ts

theorem termDisjunction_eval {M : Type} [Structure language M]
    (φ : Semiproposition language 1) (ts : List (SyntacticTerm language)) (e : ℕ → M) :
    (termDisjunction φ ts).Eval ![] e ↔ ∃ t ∈ ts, (φ/[t]).Eval ![] e := by
  induction ts with
  | nil => simp [termDisjunction, Semiformula.Eval, Semiformula.EvalAux]
  | cons t ts ih =>
      change ((φ/[t]).Eval ![] e ∨ (termDisjunction φ ts).Eval ![] e) ↔ _
      rw [ih]
      simp

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

/-- In every universal-theory model, the collected existential-rule terms
contain a witness for the open target matrix, for every free-variable valuation. -/
omit [Structure.Eq language M] in
theorem modelPreparedWitness (φ : Semiproposition language 1) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared φ axioms) (e : ℕ → M) :
    ∃ t ∈ existentialTerms p.derivation, (φ/[t]).Eval ![] e := by
  let ts := existentialTerms p.derivation
  obtain ⟨ψ,hψ,hval⟩ := boundedSound p.derivation p.cutFree p.noAll ts (fun _ h => h) e
  simp only [List.mem_cons] at hψ
  rcases hψ with rfl | hψ
  · change boundedEval ts e (Semiformula.exs φ) at hval
    rw [boundedEval.eq_8] at hval
    obtain ⟨t,ht,htval⟩ := hval
    refine ⟨t,ht,?_⟩
    have hopen' : (φ/[t]).Open := by
      change (Rew.subst ![t] ▹ φ).qr = 0
      rw [PRAFormulaParameters.qr_rew]
      exact hOpen
    exact (bounded_open_iff ts e (φ/[t]) hopen').mp htval
  · simp only [List.tilde_def, Sequent.embed, List.mem_map] at hψ
    obtain ⟨χ,hχ,hψ⟩ := hψ
    obtain ⟨σ,hσ,rfl⟩ := hχ
    subst ψ
    have hσmodel := Theory.models (T := UniversalAxiom) M (hAxioms σ hσ)
    have hσeval : (Rewriting.emb σ : Proposition language).Eval ![] e := by
      simpa [models_iff] using hσmodel
    have hneg : ¬(∼(Rewriting.emb σ : Proposition language)).Eval ![] e := by
      simpa using hσeval
    exact False.elim (hneg (bounded_implies_truth ts e _ hval))

theorem modelPreparedDisjunction (φ : Semiproposition language 1) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared φ axioms) :
    M↓[language] ⊧ (termDisjunction φ (existentialTerms p.derivation)).univCl := by
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  exact (termDisjunction_eval φ _ e).mpr (modelPreparedWitness φ hOpen axioms hAxioms p e)

end models

/-- A prepared cut-free existential sequent yields a universal-theory proof of
the finite disjunction of instances at its collected existential-rule terms. -/
theorem universal_proves_extractedDisjunction (φ : Semiproposition language 1) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared φ axioms) :
    UniversalAxiom ⊢ (termDisjunction φ (existentialTerms p.derivation)).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelPreparedDisjunction φ hOpen axioms hAxioms p

end DiophantineConsistency.HerbrandFiniteExtraction
