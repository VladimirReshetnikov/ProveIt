import DiophantineConsistency.PRAUniversalCandidate

/-! Semantic consequences of the proposed universal axiom families. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAUniversalModelLemmas
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRABooleanOps
  PRAOpenFormulaCompiler PRAOpenFormulaCoverage PRAEqualityCode PRACharacteristicBit
  PRABoundedSearchInvariant PRABoundedSearchMinimal PRAUniversalCandidate

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

theorem modelOneNeZero : (Structure.func (L := language) oneCode Fin.elim0 : M) ≠
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := Theory.models (T := UniversalAxiom) M UniversalAxiom.oneNeZero
  simp [models_iff, oneNeZeroSentence, Semiformula.eval_nrel, eqRel, applyCode, Function.comp_def] at h
  have hz : (fun i : Fin 0 => Semiterm.val ![] Empty.elim (Fin.elim0 i : TermN 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at h
  exact h

theorem modelExhaustion (x : M) :
    x = Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
      Structure.func (L := language) Code.succ
        (fun _ => Structure.func (L := language) predCode (fun _ => x)) = x := by
  have h := Theory.models (T := UniversalAxiom) M UniversalAxiom.exhaustion
  simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at h
  exact (PRAExhaustion.body_eval x (fun _ => x)).mp (h (fun _ => x) x)

theorem modelAddOne (x : M) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] =
    Structure.func (L := language) Code.succ (fun _ => x) := by
  have h := Theory.models (T := UniversalAxiom) M UniversalAxiom.addOne
  have h := (eqClosureModels _ _).mp h ![x]
  have hz : (Semiterm.val ![x] Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val ![x] Empty.elim ∘
      Fin.cases (.bvar 0) (fun _ => applyCode oneCode Fin.elim0)) =
      ![x, Structure.func (L := language) oneCode Fin.elim0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) oneCode
      (Semiterm.val ![x] Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) = _
    rw [hz]
    rfl
  change Structure.func (L := language) addCode
      (Semiterm.val ![x] Empty.elim ∘ Fin.cases (.bvar 0) (fun _ => applyCode oneCode Fin.elim0)) =
    Structure.func (L := language) Code.succ
      (Semiterm.val ![x] Empty.elim ∘ fun _ : Fin 1 => (.bvar 0 : TermN 1)) at h
  rw [hv] at h
  exact h

theorem modelCompiledBit {n : ℕ} (p : OpenFormula n) (e : Fin n → M) :
    IsBit (Structure.func (L := language) (compileFormula equalityCode p) e) := by
  have h := Theory.models (T := UniversalAxiom) M (UniversalAxiom.characteristicBit p)
  simp only [models_iff, bitSentence, Semiformula.eval_allClosure] at h
  have h := h e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _ at h
  simp [Semiformula.EvalAux, eqRel, applyCode, vars, Function.comp_def] at h
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at h
  exact h

theorem modelCompiledCorrect {n : ℕ} (p : OpenFormula n) (e : Fin n → M) :
    Structure.func (L := language) (compileFormula equalityCode p) e =
      Structure.func (L := language) oneCode Fin.elim0 ↔ (asFormula p).Eval e Empty.elim := by
  have h := Theory.models (T := UniversalAxiom) M (UniversalAxiom.characteristicCorrect p)
  simp only [models_iff, formulaCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff] at h
  have h := h e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _ at h
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, vars, Function.comp_def] at h
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at h
  simp only [←Semiformula.neg_eq, Semiformula.EvalAux_neg] at h
  change (¬(Structure.func (L := language) (compileFormula equalityCode p) e =
      Structure.func (L := language) oneCode Fin.elim0) ∨ (asFormula p).Eval e Empty.elim) ∧
    (¬(asFormula p).Eval e Empty.elim ∨ Structure.func (L := language) (compileFormula equalityCode p) e =
      Structure.func (L := language) oneCode Fin.elim0) at h
  tauto

end models
end DiophantineConsistency.PRAUniversalModelLemmas
