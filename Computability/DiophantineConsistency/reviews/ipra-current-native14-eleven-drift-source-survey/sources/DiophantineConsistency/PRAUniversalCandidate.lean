import DiophantineConsistency.PRABoundedSearchUniversalRule

/-! A candidate universal presentation assembled from certified search axioms.
The reverse interpretation of open induction is a separate theorem. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAUniversalCandidate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion
  PRAOpenFormulaCompiler PRAEqualityCode PRACharacteristicBit PRANonzeroCharacter
  PRABoundedSearchInvariant PRABoundedSearchMinimal

def oneNeZeroSentence : Sentence language :=
  Semiformula.nrel Language.ORing.Rel.eq
    ![applyCode oneCode Fin.elim0, applyCode (Code.zero 0) Fin.elim0]

theorem PRA_proves_oneNeZero : PRA ⊢ oneNeZeroSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp [models_iff, oneNeZeroSentence, Semiformula.eval_nrel, eqRel, applyCode, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val ![] Empty.elim (Fin.elim0 i : TermN 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  exact modelOneNeZero (M := M)

/-- Explicit axiom families for the proposed universal presentation. -/
inductive UniversalAxiom : Theory language
  | equality (σ : Sentence language) : σ ∈ 𝗘𝗤 language → UniversalAxiom σ
  | defining (σ : Sentence language) : DefiningEquation σ → UniversalAxiom σ
  | basic (σ : Sentence language) : BasicAxiom σ → UniversalAxiom σ
  | exhaustion : UniversalAxiom exhaustionSentence
  | oneNeZero : UniversalAxiom oneNeZeroSentence
  | addOne : UniversalAxiom addOneSentence
  | searchCandidate {n : ℕ} (good : Code (n+1)) : UniversalAxiom (candidateSentence good)
  | searchMinimal {n : ℕ} (good : Code (n+1)) : UniversalAxiom (minimalSentence good)
  | characteristicBit {n : ℕ} (p : OpenFormula n) :
      UniversalAxiom (bitSentence (compileFormula equalityCode p))
  | characteristicCorrect {n : ℕ} (p : OpenFormula n) :
      UniversalAxiom (formulaCorrectSentence equalityCode p)

/-- Each proposed universal-presentation axiom is a theorem of candidate PRA. -/
theorem PRA_proves_universalAxiom {σ : Sentence language} (h : UniversalAxiom σ) : PRA ⊢ σ := by
  cases h with
  | equality σ hσ => exact Entailment.by_axm (Or.inl (Or.inl (Or.inl hσ)))
  | defining σ hσ => exact Entailment.by_axm (Or.inl (Or.inl (Or.inr hσ)))
  | basic σ hσ => exact Entailment.by_axm (Or.inr hσ)
  | exhaustion => exact PRA_proves_exhaustion
  | oneNeZero => exact PRA_proves_oneNeZero
  | addOne => exact PRA_proves_addOne
  | searchCandidate good => exact PRA_proves_candidateSentence good
  | searchMinimal good => exact PRA_proves_minimalSentence good
  | characteristicBit p => exact PRA_proves_compiledBit p
  | characteristicCorrect p =>
      exact PRA_proves_formulaCorrect equalityCode p PRA_proves_equalityBit PRA_proves_equalityCorrect

end DiophantineConsistency.PRAUniversalCandidate
