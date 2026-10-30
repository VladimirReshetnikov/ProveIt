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

/-- The three bound slots are followed by the free parameter values. -/
theorem parameterTripleMatrix_eval {M : Type} [Structure language M] {n : ℕ}
    (φ : Semisentence language (n+3)) (e : ℕ → M) (x y z : M) :
    (parameterTripleMatrix φ).Eval ![x,y,z] e ↔
      φ.Eval (Fin.cases x (Fin.cases y (Fin.cases z (fun i : Fin n => e i.val)))) Empty.elim := by
  unfold parameterTripleMatrix
  rw [Semiformula.eval_rew_q]
  simp only [Function.comp_def, Rew.q_fvar, Semiterm.val_bShift]
  have hb : (fun i => Semiterm.val ![y,z] e
      ((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))).q.q #i)) =
      Fin.cases y (Fin.cases z (fun i : Fin n => e i.val)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · change Semiterm.val _ _ ((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))).q.q #((0 : Fin (n+1)).succ)) = _
        simp only [Rew.q_bvar_succ, Rew.q_bvar_zero, Semiterm.val_bShift, Semiterm.val_bvar]
        rfl
      · change Semiterm.val _ _ ((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))).q.q #(k.succ.succ)) = _
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar, Semiterm.val_bShift, Semiterm.val_fvar]
        rfl
  have hf : (fun i : Empty => Semiterm.val ![] e (Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language)) &i)) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]
  rfl


theorem parameterTripleMatrix_open {n : ℕ} (φ : Semisentence language (n+3))
    (hφ : φ.Open) : (parameterTripleMatrix φ).Open := by
  change (parameterTripleMatrix φ).qr = 0
  unfold parameterTripleMatrix
  rw [PRAFormulaParameters.qr_rew]
  exact hφ

noncomputable def prepareAllTriple {n : ℕ} (φ : Semisentence language (n+3)) (hOpen : φ.Open)
    (p : Theory.Proof UniversalAxiom (∀⁰* ∃⁰ ∃⁰ ∃⁰ φ)) :
    Prepared (∃⁰ ∃⁰ (parameterTripleMatrix φ)) p.axioms := by
  have hopen := parameterTripleMatrix_open φ hOpen
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
  have hopen := parameterTripleMatrix_open φ hOpen
  exact universal_proves_preparedTripleDisjunction (parameterTripleMatrix φ) hopen p.axioms p.axioms_mem (prepareAllTriple φ hOpen p)
/-- An actual candidate-PRA theorem yields a specific finite disjunction. -/
theorem candidate_proves_parameterTripleDisjunction {n : ℕ}
    (φ : Semisentence language (n+3)) (hOpen : φ.Open)
    (h : PRATheory.PRA ⊢ (∀⁰* ∃⁰ ∃⁰ ∃⁰ φ)) :
    ∃ p : Theory.Proof UniversalAxiom (∀⁰* ∃⁰ ∃⁰ ∃⁰ φ),
      PRATheory.PRA ⊢ (tripleDisjunction (parameterTripleMatrix φ)
        (existentialTerms (prepareAllTriple φ hOpen p).derivation)).univCl := by
  obtain ⟨p⟩ := PRAUniversalEquivalence.universal_proves_candidate h
  exact ⟨p, PRAUniversalEquivalence.candidate_proves_universal
    (universal_proves_parameterTripleDisjunction φ hOpen p)⟩
end DiophantineConsistency.HerbrandTripleParameterized
