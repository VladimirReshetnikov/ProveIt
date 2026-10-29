import DiophantineConsistency.HerbrandFiniteExtraction

/-! Finite-term extraction for an unpaired triple existential over an open matrix. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandTripleExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAUniversalCandidate HerbrandExistentialSequents HerbrandUniversalPreparation
  HerbrandBoundedSemantics HerbrandBoundedSoundness HerbrandBoundedTruth

def afterFirst (φ : Semiproposition language 3) (t : SyntacticTerm language) : Semiproposition language 2 :=
  (Rew.subst ![t]).qpow 2 ▹ φ

def afterSecond (φ : Semiproposition language 3) (t u : SyntacticTerm language) : Semiproposition language 1 :=
  (Rew.subst ![u]).q ▹ afterFirst φ t

def tripleInstance (φ : Semiproposition language 3) (t u v : SyntacticTerm language) : Proposition language :=
  (afterSecond φ t u)/[v]

/-- Cut elimination for a triple-existential sequent preserves the finite
universal axioms and contains no universal-rule nodes. -/
noncomputable def prepareTriple (φ : Semiproposition language 3) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (d : Derivation ((∃⁰ ∃⁰ ∃⁰ φ) :: ∼Sequent.embed axioms)) :
    Prepared (∃⁰ ∃⁰ φ) axioms := by
  let dd := Derivation.Canonical.hauptsatz d
  have hn : NoUniversal φ := noUniversal_of_open φ hOpen
  have hg : ∀ ψ ∈ (∃⁰ ∃⁰ ∃⁰ φ) :: ∼Sequent.embed axioms, NoUniversal ψ := by
    intro ψ hψ
    simp only [List.mem_cons] at hψ
    rcases hψ with rfl | hψ
    · exact hn
    · simp only [List.tilde_def, Sequent.embed, List.mem_map] at hψ
      obtain ⟨χ,hχ,hψ⟩ := hψ
      obtain ⟨σ,hσ,rfl⟩ := hχ
      subst ψ
      exact negatedAxiom_noUniversal σ (hAxioms σ hσ)
  exact ⟨dd.val, dd.property, cutFree_noUniversalRule dd.val dd.property hg⟩

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

omit [Structure.Eq language M] in
theorem modelTripleWitness (φ : Semiproposition language 3) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared (∃⁰ ∃⁰ φ) axioms) (e : ℕ → M) :
    ∃ t ∈ existentialTerms p.derivation, ∃ u ∈ existentialTerms p.derivation,
      ∃ v ∈ existentialTerms p.derivation, (tripleInstance φ t u v).Eval ![] e := by
  let ts := existentialTerms p.derivation
  obtain ⟨ψ,hψ,hval⟩ := boundedSound p.derivation p.cutFree p.noAll ts (fun _ h => h) e
  simp only [List.mem_cons] at hψ
  rcases hψ with rfl | hψ
  · change boundedEval ts e (∃⁰ ∃⁰ ∃⁰ φ) at hval
    have hx := boundedEval.eq_8 ts e (∃⁰ ∃⁰ φ)
    have hval' := (Iff.of_eq hx).mp hval
    obtain ⟨t,ht,h₁⟩ := hval'
    have h₁' : boundedEval ts e (∃⁰ ∃⁰ afterFirst φ t) := by
      simpa [afterFirst, Rewriting.subst, Rew.qpow_succ] using h₁
    change boundedEval ts e (Semiformula.exs (∃⁰ afterFirst φ t)) at h₁'
    have h₁'' := (Iff.of_eq (boundedEval.eq_8 ts e (∃⁰ afterFirst φ t))).mp h₁'
    obtain ⟨u,hu,h₂⟩ := h₁''
    have h₂' : boundedEval ts e (∃⁰ afterSecond φ t u) := by
      simpa [afterSecond, Rewriting.subst] using h₂
    change boundedEval ts e (Semiformula.exs (afterSecond φ t u)) at h₂'
    have h₂'' := (Iff.of_eq (boundedEval.eq_8 ts e (afterSecond φ t u))).mp h₂'
    obtain ⟨v,hv,h₃⟩ := h₂''
    refine ⟨t,ht,u,hu,v,hv,?_⟩
    apply (bounded_open_iff ts e (tripleInstance φ t u v) ?_).mp
    · exact h₃
    · change (Rew.subst ![v] ▹ ((Rew.subst ![u]).q ▹ ((Rew.subst ![t]).qpow 2 ▹ φ))).qr = 0
      rw [PRAFormulaParameters.qr_rew, PRAFormulaParameters.qr_rew, PRAFormulaParameters.qr_rew]
      exact hOpen
  · simp only [List.tilde_def, Sequent.embed, List.mem_map] at hψ
    obtain ⟨χ,hχ,hψ⟩ := hψ
    obtain ⟨σ,hσ,rfl⟩ := hχ
    subst ψ
    have hσmodel := Theory.models (T := UniversalAxiom) M (hAxioms σ hσ)
    have hσeval : (Rewriting.emb σ : Proposition language).Eval ![] e := by
      simpa [models_iff] using hσmodel
    have hneg : ¬(∼(Rewriting.emb σ : Proposition language)).Eval ![] e := by simpa using hσeval
    exact False.elim (hneg (bounded_implies_truth ts e _ hval))

end models
end DiophantineConsistency.HerbrandTripleExtraction
