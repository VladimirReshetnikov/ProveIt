import DiophantineConsistency.PRAUniversalSyntax

/-! Verify the universal-prefix shape of the proposed presentation. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAUniversalAxiomSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRAUniversalCandidate
  PRAUniversalSyntax PRAOpenFormulaCompiler PRAEqualityCode PRACharacteristicBit
  PRABoundedSearchInvariant PRABoundedSearchMinimal

private theorem conj_open {ξ : Type} {n k : ℕ} (v : Fin k → Semiformula language ξ n)
    (h : ∀ i, (v i).Open) : (Matrix.conj v).Open := by
  induction k with
  | zero => simp [Matrix.conj, Semiformula.Open]
  | succ k ih =>
    simp only [Matrix.conj, Semiformula.Open, Semiformula.qr_and, Nat.max_eq_zero_iff]
    exact ⟨h 0, ih (fun i => v i.succ) (fun i => h i.succ)⟩

private theorem equalClosure_universal {n : ℕ} (a b : TermN n) :
    UniversalPrefix (equalClosure a b) := by
  apply universalPrefix_allClosure
  simp [UniversalPrefix, Semiformula.Open]

private theorem defining_universal {σ : Sentence language} (h : DefiningEquation σ) : UniversalPrefix σ := by
  cases h with
  | zero n => exact equalClosure_universal _ _
  | projection i => exact equalClosure_universal _ _
  | composition f g => exact equalClosure_universal _ _
  | recursionBase f g => exact equalClosure_universal _ _
  | recursionStep f g => exact equalClosure_universal _ _

private theorem equality_universal {σ : Sentence language} (h : σ ∈ 𝗘𝗤 language) : UniversalPrefix σ := by
  cases h with
  | refl => rfl
  | symm => rfl
  | trans => rfl
  | funcExt f =>
      apply universalPrefix_allClosure
      simp only [UniversalPrefix, Semiformula.Open, Semiformula.qr_imply, Nat.max_eq_zero_iff]
      constructor
      · apply conj_open
        intro i
        rfl
      · rfl
  | relExt r =>
      apply universalPrefix_allClosure
      simp only [UniversalPrefix, Semiformula.Open, Semiformula.qr_imply, Semiformula.qr_rel,
        Nat.max_eq_zero_iff, and_true]
      apply conj_open
      intro i
      rfl

theorem universalAxiom_isUniversal {σ : Sentence language} (h : UniversalAxiom σ) : UniversalPrefix σ := by
  cases h with
  | equality σ h => exact equality_universal h
  | defining σ h => exact defining_universal h
  | basic σ h =>
      cases h with
      | succNonzero => sorry
      | succInjective => sorry
      | orderDefinition => sorry
  | exhaustion => sorry
  | oneNeZero => sorry
  | addOne => sorry
  | searchCandidate good => sorry
  | searchMinimal good => sorry
  | characteristicBit p => sorry
  | characteristicCorrect p => sorry

end DiophantineConsistency.PRAUniversalAxiomSyntax
