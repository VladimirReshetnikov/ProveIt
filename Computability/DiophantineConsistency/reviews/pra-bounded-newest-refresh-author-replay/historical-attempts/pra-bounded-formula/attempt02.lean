import DiophantineConsistency.PRABoundedBoolean

/-! A compositional bounded-formula syntax and candidate-PRA characteristic codes. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedFormula
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRACharacteristicBit PRAOpenFormulaCoverage
  PRABoundedCharacteristic PRABoundedTermCharacteristic PRABoundedExistential PRABoundedBoolean

inductive BoundedFormula : ℕ → Type
  | openFormula {n : ℕ} (φ : Semisentence language n) (h : φ.Open) : BoundedFormula n
  | and {n : ℕ} (φ ψ : BoundedFormula n) : BoundedFormula n
  | or {n : ℕ} (φ ψ : BoundedFormula n) : BoundedFormula n
  | all {n : ℕ} (t : TermN n) (φ : BoundedFormula (n+1)) : BoundedFormula n
  | ex {n : ℕ} (t : TermN n) (φ : BoundedFormula (n+1)) : BoundedFormula n

def asFormula : {n : ℕ} → BoundedFormula n → Semisentence language n
  | _, .openFormula φ _ => φ
  | _, .and φ ψ => asFormula φ ⋏ asFormula ψ
  | _, .or φ ψ => asFormula φ ⋎ asFormula ψ
  | _, .all t φ => ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, Rew.bShift t])] asFormula φ
  | _, .ex t φ => ∃⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, Rew.bShift t])] asFormula φ

theorem hasCharacteristic {n : ℕ} (p : BoundedFormula n) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧ PRA ⊢ oneCorrectSentence c (asFormula p) := by
  induction p with
  | openFormula φ h =>
      obtain ⟨c,hpr,hbit,hcorrect⟩ := PRA_proves_openBooleanCharacteristic φ h
      exact ⟨c,hpr,hbit,hcorrect⟩
  | and φ ψ ihφ ihψ =>
      obtain ⟨c,_,hcbit,hc⟩ := ihφ
      obtain ⟨d,_,hdbit,hd⟩ := ihψ
      obtain ⟨hbit,hcorrect⟩ := PRA_andCharacteristic c d (asFormula φ) (asFormula ψ) hcbit hdbit hc hd
      exact ⟨PRAOpenFormulaCompiler.andCode c d, eval_primrec _, hbit, hcorrect⟩
  | or φ ψ ihφ ihψ =>
      obtain ⟨c,_,hcbit,hc⟩ := ihφ
      obtain ⟨d,_,hdbit,hd⟩ := ihψ
      obtain ⟨k,hbit,hcorrect⟩ := PRA_orCharacteristic c d (asFormula φ) (asFormula ψ) hcbit hdbit hc hd
      exact ⟨k,eval_primrec _,hbit,hcorrect⟩
  | all t φ ih =>
      obtain ⟨c,_,hbit,hcorrect⟩ := ih
      obtain ⟨d,hpr,hdbit,hdcorrect⟩ := PRA_boundedTermStep c (asFormula φ) t hbit hcorrect
      refine ⟨d,hpr,hdbit,?_⟩
      simpa [asFormula, termBoundedBy_eq] using hdcorrect
  | ex t φ ih =>
      obtain ⟨c,_,hbit,hcorrect⟩ := ih
      exact PRA_boundedTermExistentialStep c (asFormula φ) t hbit hcorrect

end DiophantineConsistency.PRABoundedFormula
