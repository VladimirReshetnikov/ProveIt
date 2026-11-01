import DiophantineConsistency.PRAFormulaParameters

/-! Certified characteristic codes are also provably Boolean in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRACharacteristicBit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABooleanOps PRAOpenFormulaCompiler
  PRAOpenFormulaCoverage PRAEqualityCode PRAFormulaParameters

def bitSentence {n : ℕ} (c : Code n) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode c (vars n), applyCode (Code.zero 0) Fin.elim0]) ⋎
    (Semiformula.rel Language.ORing.Rel.eq
      ![applyCode c (vars n), applyCode oneCode Fin.elim0]) : Semisentence language n)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [M↓[language] ⊧* PRA] in
theorem bitSentence_iff {n : ℕ} (c : Code n) :
    M↓[language] ⊧ bitSentence c ↔
      ∀ e : Fin n → M, IsBit (Structure.func (L := language) c e) := by
  simp only [models_iff, bitSentence, Semiformula.eval_allClosure]
  apply forall_congr'
  intro e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _ ↔ _
  simp [Semiformula.EvalAux, eqRel, applyCode, vars, Function.comp_def, IsBit]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]

theorem modelCompiledBit {n : ℕ} (p : OpenFormula n) :
    M↓[language] ⊧ bitSentence (compileFormula equalityCode p) := by
  apply (bitSentence_iff _).mpr
  intro e
  exact (modelCompileFormula equalityCode (modelEqualityCode (M := M)) p e).1

end models

/-- The compiler's output is provably 0 or 1 in candidate PRA. -/
theorem PRA_proves_compiledBit {n : ℕ} (p : OpenFormula n) :
    PRA ⊢ bitSentence (compileFormula equalityCode p) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelCompiledBit p

/-- Every Foundation open semisentence has a fixed PR characteristic code
whose Boolean range and correctness are both provable in candidate PRA. -/
theorem PRA_proves_openBooleanCharacteristic {n : ℕ} (φ : Semisentence language n)
    (h : φ.Open) : ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧
      PRA ⊢ characteristicSentence c φ := by
  obtain ⟨p, _, hp⟩ := parseFormula_open φ h
  subst φ
  refine ⟨compileFormula equalityCode p, eval_primrec _, PRA_proves_compiledBit p, ?_⟩
  exact PRA_proves_formulaCorrect equalityCode p PRA_proves_equalityBit PRA_proves_equalityCorrect

/-- The same result with all free parameters explicitly packed into the code's
finite argument vector. -/
theorem PRA_proves_packedOpenBooleanCharacteristic {n : ℕ} (φ : Semiproposition language n)
    (h : φ.Open) : ∃ c : Code (n + φ.fvSup), Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧
      PRA ⊢ characteristicSentence c (packParameters φ) :=
  PRA_proves_openBooleanCharacteristic (packParameters φ) (packParameters_open φ h)

end DiophantineConsistency.PRACharacteristicBit
