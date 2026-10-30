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

/-- Prepare the concrete proof of a closed triple-existential theorem. -/
noncomputable def prepareTripleClosed (φ : Semisentence language 3) (hOpen : φ.Open)
    (p : Theory.Proof UniversalAxiom (∃⁰ ∃⁰ ∃⁰ φ)) : Prepared (∃⁰ ∃⁰ (Rewriting.emb φ)) p.axioms := by
  have hopen : (Rewriting.emb φ : Semiproposition language 3).Open := by
    change (Rewriting.emb φ : Semiproposition language 3).qr = 0
    rw [PRAFormulaParameters.qr_rew]
    exact hOpen
  apply prepareTriple (Rewriting.emb φ) hopen p.axioms p.axioms_mem
  have d := p.derivation
  change Derivation (((∃⁰ ∃⁰ ∃⁰ φ) :: ∼p.axioms).map Rewriting.emb) at d
  simpa [Sequent.embed] using d

def triples (ts : List (SyntacticTerm language)) : List (SyntacticTerm language × SyntacticTerm language × SyntacticTerm language) :=
  ts.flatMap (fun t => ts.flatMap (fun u => ts.map (fun v => (t,u,v))))

def tripleDisjunction (φ : Semiproposition language 3) (ts : List (SyntacticTerm language)) : Proposition language :=
  (triples ts).foldr (fun p acc => tripleInstance φ p.1 p.2.1 p.2.2 ⋎ acc) ⊥

theorem tripleDisjunction_eval {M : Type} [Structure language M]
    (φ : Semiproposition language 3) (ts : List (SyntacticTerm language)) (e : ℕ → M) :
    (tripleDisjunction φ ts).Eval ![] e ↔
      ∃ t ∈ ts, ∃ u ∈ ts, ∃ v ∈ ts, (tripleInstance φ t u v).Eval ![] e := by
  have hfold : ∀ (xs : List (SyntacticTerm language × SyntacticTerm language × SyntacticTerm language)),
      (xs.foldr (fun p acc => tripleInstance φ p.1 p.2.1 p.2.2 ⋎ acc) ⊥).Eval ![] e ↔
        ∃ p ∈ xs, (tripleInstance φ p.1 p.2.1 p.2.2).Eval ![] e := by
    intro xs
    induction xs with
    | nil => simp [Semiformula.Eval]
    | cons p ps ih =>
      change ((tripleInstance φ p.1 p.2.1 p.2.2).Eval ![] e ∨
        (ps.foldr (fun p acc => tripleInstance φ p.1 p.2.1 p.2.2 ⋎ acc) ⊥).Eval ![] e) ↔ _
      rw [ih]
      simp
  rw [tripleDisjunction, hfold]
  simp [triples]
  constructor
  · rintro ⟨t,u,v,⟨ht,hu,hv⟩,h⟩
    exact ⟨t,ht,u,hu,v,hv,h⟩
  · rintro ⟨t,ht,u,hu,v,hv,h⟩
    exact ⟨t,u,v,⟨ht,hu,hv⟩,h⟩

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

set_option linter.unusedVariables false in
omit [Structure.Eq language M] in
theorem modelTripleWitness (φ : Semiproposition language 3) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared (∃⁰ ∃⁰ φ) axioms) (e : ℕ → M) :
    ∃ t ∈ existentialTerms p.derivation, ∃ u ∈ existentialTerms p.derivation,
      ∃ v ∈ existentialTerms p.derivation, (tripleInstance φ t u v).Eval ![] e := by
  let ts := existentialTerms p.derivation
  have hval := HerbrandFiniteExtraction.modelPreparedBounded (∃⁰ ∃⁰ φ) axioms hAxioms p e
  change boundedEval ts e (∃⁰ ∃⁰ ∃⁰ φ) at hval
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
  exact bounded_implies_truth ts e (tripleInstance φ t u v) h₃

omit [Structure.Eq language M] in
theorem modelTripleDisjunction (φ : Semiproposition language 3) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared (∃⁰ ∃⁰ φ) axioms) :
    M↓[language] ⊧ (tripleDisjunction φ (existentialTerms p.derivation)).univCl := by
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  exact (tripleDisjunction_eval φ _ e).mpr (modelTripleWitness φ hOpen axioms hAxioms p e)

end models

/-- A prepared triple-existential sequent, with arbitrary free parameters,
yields a universal-theory proof of the finite triple-instance disjunction. -/
theorem universal_proves_preparedTripleDisjunction (φ : Semiproposition language 3) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared (∃⁰ ∃⁰ φ) axioms) :
    UniversalAxiom ⊢ (tripleDisjunction φ (existentialTerms p.derivation)).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelTripleDisjunction φ hOpen axioms hAxioms p

/-- A universal-theory proof of a closed triple existential over an open
matrix yields a proof of the extracted finite disjunction of triple instances. -/
theorem universal_proves_tripleDisjunction (φ : Semisentence language 3) (hOpen : φ.Open)
    (p : Theory.Proof UniversalAxiom (∃⁰ ∃⁰ ∃⁰ φ)) :
    UniversalAxiom ⊢ (tripleDisjunction (Rewriting.emb φ)
      (existentialTerms (prepareTripleClosed φ hOpen p).derivation)).univCl := by
  have hopen : (Rewriting.emb φ : Semiproposition language 3).Open := by
    change (Rewriting.emb φ : Semiproposition language 3).qr = 0
    rw [PRAFormulaParameters.qr_rew]
    exact hOpen
  exact universal_proves_preparedTripleDisjunction (Rewriting.emb φ) hopen
    p.axioms p.axioms_mem (prepareTripleClosed φ hOpen p)

end DiophantineConsistency.HerbrandTripleExtraction
