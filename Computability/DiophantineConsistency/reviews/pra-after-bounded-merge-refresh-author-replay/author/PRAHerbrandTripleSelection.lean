import DiophantineConsistency.PRAFiniteTripleChoice
import DiophantineConsistency.PRAHerbrandSelection
/-! Coordinated PR selection from an open-formula triple disjunction. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAHerbrandTripleSelection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAEqualityCode
  PRAOpenFormulaCompiler PRACharacteristicBit PRAFiniteTripleChoice PRAHerbrandSelection
  PRAUniversalCandidate PRAUniversalEquivalence

def matrixAt {n : ℕ} (φ : Semisentence language (n+3)) (t : Triple n) : Semisentence language n :=
  φ ⇜ Fin.cases (applyCode t.first (vars n)) (Fin.cases (applyCode t.second (vars n))
    (Fin.cases (applyCode t.third (vars n)) (vars n)))

def matrixList {n : ℕ} (φ : Semisentence language (n+3)) (fallback : Triple n) : List (Triple n) → Semisentence language n
  | [] => matrixAt φ fallback
  | t :: ts => matrixAt φ t ⋎ matrixList φ fallback ts

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelMatrixAt {n : ℕ} (p : OpenFormula (n+3)) (t : Triple n) (e : Fin n → M) :
    (matrixAt (asFormula p) t).Eval e Empty.elim ↔
      (tripleFormula (compileFormula equalityCode p) t).Eval e Empty.elim := by
  rw [modelTripleFormula, modelApplyTriple]
  have hc := (modelCompileFormula equalityCode (modelEqualityCode (M := M)) p
    (Fin.cases (Structure.func (L := language) t.first e)
      (Fin.cases (Structure.func (L := language) t.second e)
        (Fin.cases (Structure.func (L := language) t.third e) e)))).2
  rw [formulaHolds_eval] at hc
  rw [matrixAt, Semiformula.eval_substs]
  have hv : (Semiterm.val e Empty.elim ∘ Fin.cases (applyCode t.first (vars n))
      (Fin.cases (applyCode t.second (vars n)) (Fin.cases (applyCode t.third (vars n)) (vars n)))) =
      Fin.cases (Structure.func (L := language) t.first e)
        (Fin.cases (Structure.func (L := language) t.second e)
          (Fin.cases (Structure.func (L := language) t.third e) e)) := by
    have hv : (Semiterm.val e Empty.elim ∘ vars n) = e := by funext i; rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) t.first (Semiterm.val e Empty.elim ∘ vars n) = _
      rw [hv]
      rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · change Structure.func (L := language) t.second (Semiterm.val e Empty.elim ∘ vars n) = _
        rw [hv]
        rfl
      · refine Fin.cases ?_ (fun _ => rfl) k
        change Structure.func (L := language) t.third (Semiterm.val e Empty.elim ∘ vars n) = _
        rw [hv]
        rfl
  rw [hv]
  exact hc.symm

theorem modelMatrixList {n : ℕ} (p : OpenFormula (n+3)) (fallback : Triple n)
    (ts : List (Triple n)) (e : Fin n → M) :
    (matrixList (asFormula p) fallback ts).Eval e Empty.elim ↔
      (PRAFiniteTripleChoice.listFormula (compileFormula equalityCode p) fallback ts).Eval e Empty.elim := by
  induction ts with
  | nil => exact modelMatrixAt p fallback e
  | cons t ts ih => simpa [matrixList, PRAFiniteTripleChoice.listFormula] using or_congr (modelMatrixAt p t e) ih
end models

theorem PRA_exists_triple_of_openDisjunction {n : ℕ} (φ : Semisentence language (n+3))
    (hOpen : φ.Open) (fallback : Triple n) (ts : List (Triple n))
    (hEither : PRA ⊢ (∀⁰* matrixList φ fallback ts)) :
    ∃ t : Triple n, Primrec (eval t.first) ∧ Primrec (eval t.second) ∧ Primrec (eval t.third) ∧
      PRA ⊢ (∀⁰* matrixAt φ t) := by
  obtain ⟨p, _, hp⟩ := PRAOpenFormulaCoverage.parseFormula_open φ hOpen
  subst φ
  have hList : PRA ⊢ PRAFiniteTripleChoice.listSentence (compileFormula equalityCode p) fallback ts := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hEither
    simp only [models_iff, Semiformula.eval_allClosure] at hm
    simp only [models_iff, PRAFiniteTripleChoice.listSentence, Semiformula.eval_allClosure]
    intro e
    exact (modelMatrixList p fallback ts e).mp (hm e)
  obtain ⟨t,h1,h2,h3,hSel⟩ := PRA_exists_tripleListChoice (compileFormula equalityCode p) fallback ts
    (PRA_proves_compiledBit p) hList
  refine ⟨t,h1,h2,h3,?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hSel
  simp only [models_iff, Semiformula.eval_allClosure] at hm ⊢
  intro e
  exact (modelMatrixAt p t e).mpr (hm e)
end DiophantineConsistency.PRAHerbrandTripleSelection
