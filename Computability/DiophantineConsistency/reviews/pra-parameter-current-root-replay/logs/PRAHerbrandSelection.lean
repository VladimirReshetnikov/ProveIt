import DiophantineConsistency.PRAFiniteWitnessList
import DiophantineConsistency.PRAUniversalEquivalence

/-! Select one PR witness from an actual open-matrix disjunction. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAHerbrandSelection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAEqualityCode
  PRAOpenFormulaCompiler PRACharacteristicBit PRAFiniteWitnessChoice PRAFiniteWitnessList
  PRAUniversalCandidate PRAUniversalEquivalence

/-- Substitute a PR witness and all parameters into an open matrix. -/
def matrixAt {n : ℕ} (p : OpenFormula (n+1)) (w : Code n) : Semisentence language n :=
  asFormula p ⇜ Fin.cases (applyCode w (vars n)) (vars n)

def matrixList {n : ℕ} (p : OpenFormula (n+1)) (fallback : Code n) : List (Code n) → Semisentence language n
  | [] => matrixAt p fallback
  | w :: ws => matrixAt p w ⋎ matrixList p fallback ws

def matrixListSentence {n : ℕ} (p : OpenFormula (n+1)) (fallback : Code n) (ws : List (Code n)) : Sentence language :=
  ∀⁰* matrixList p fallback ws

def matrixSelectedSentence {n : ℕ} (p : OpenFormula (n+1)) (w : Code n) : Sentence language :=
  ∀⁰* matrixAt p w

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelMatrixAt {n : ℕ} (p : OpenFormula (n+1)) (w : Code n) (e : Fin n → M) :
    (matrixAt p w).Eval e Empty.elim ↔
      (witnessFormula (compileFormula equalityCode p) w).Eval e Empty.elim := by
  rw [modelWitnessFormula, modelApplyWitness]
  have hc := (modelCompileFormula equalityCode (modelEqualityCode (M := M)) p
    (Fin.cases (Structure.func (L := language) w e) e)).2
  rw [formulaHolds_eval] at hc
  rw [matrixAt, Semiformula.eval_substs]
  have hv : (Semiterm.val e Empty.elim ∘
      Fin.cases (applyCode w (vars n)) (vars n)) =
      Fin.cases (Structure.func (L := language) w e) e := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) w (Semiterm.val e Empty.elim ∘ vars n) = _
      have h : (Semiterm.val e Empty.elim ∘ vars n) = e := by funext i; rfl
      rw [h]
      rfl
    · rfl
  rw [hv]
  exact hc.symm

theorem modelMatrixList {n : ℕ} (p : OpenFormula (n+1)) (fallback : Code n)
    (ws : List (Code n)) (e : Fin n → M) :
    (matrixList p fallback ws).Eval e Empty.elim ↔
      (listFormula (compileFormula equalityCode p) fallback ws).Eval e Empty.elim := by
  induction ws with
  | nil => exact modelMatrixAt p fallback e
  | cons w ws ih =>
      simpa [matrixList, listFormula] using or_congr (modelMatrixAt p w e) ih

theorem modelMatrixListSentence {n : ℕ} (p : OpenFormula (n+1)) (fallback : Code n)
    (ws : List (Code n)) (h : M↓[language] ⊧ matrixListSentence p fallback ws) :
    M↓[language] ⊧ listSentence (compileFormula equalityCode p) fallback ws := by
  simp only [models_iff, matrixListSentence, Semiformula.eval_allClosure] at h
  simp only [models_iff, listSentence, Semiformula.eval_allClosure]
  intro e
  exact (modelMatrixList p fallback ws e).mp (h e)

theorem modelMatrixSelectedSentence {n : ℕ} (p : OpenFormula (n+1)) (w : Code n)
    (h : M↓[language] ⊧ (∀⁰* witnessFormula (compileFormula equalityCode p) w)) :
    M↓[language] ⊧ matrixSelectedSentence p w := by
  simp only [models_iff, Semiformula.eval_allClosure] at h
  simp only [models_iff, matrixSelectedSentence, Semiformula.eval_allClosure]
  intro e
  exact (modelMatrixAt p w e).mpr (h e)

end models

/-- A universal-theory proof of an actual finite open-matrix disjunction gives
one fixed PR witness and a closed candidate-PRA proof of that matrix at the
selected witness. Producing the finite disjunction remains a separate Herbrand
extraction obligation. -/
theorem PRA_exists_witness_of_matrixDisjunction {n : ℕ} (p : OpenFormula (n+1))
    (fallback : Code n) (ws : List (Code n))
    (hEither : UniversalAxiom ⊢ matrixListSentence p fallback ws) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ matrixSelectedSentence p c := by
  have hPRA : PRA ⊢ matrixListSentence p fallback ws := candidate_proves_universal hEither
  have hList : PRA ⊢ listSentence (compileFormula equalityCode p) fallback ws := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelMatrixListSentence p fallback ws
      (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hPRA)
  obtain ⟨c,hPR,hSel⟩ := PRA_exists_listWitness (compileFormula equalityCode p) fallback ws
    (PRA_proves_compiledBit p) hList
  refine ⟨c,hPR,?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMatrixSelectedSentence p c
    (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hSel)

/-- The same witness substitution for any actual Foundation semisentence. -/
def openMatrixAt {n : ℕ} (φ : Semisentence language (n+1)) (w : Code n) : Semisentence language n :=
  φ ⇜ Fin.cases (applyCode w (vars n)) (vars n)

def openMatrixList {n : ℕ} (φ : Semisentence language (n+1)) (fallback : Code n) :
    List (Code n) → Semisentence language n
  | [] => openMatrixAt φ fallback
  | w :: ws => openMatrixAt φ w ⋎ openMatrixList φ fallback ws

theorem openMatrixList_asFormula {n : ℕ} (p : OpenFormula (n+1)) (fallback : Code n)
    (ws : List (Code n)) : openMatrixList (asFormula p) fallback ws = matrixList p fallback ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [openMatrixList, matrixList, openMatrixAt, matrixAt, ih]

/-- For any actual Foundation open matrix, a universal-theory proof of a
finite disjunction of candidate instances yields a fixed PR witness and a
candidate-PRA proof of that matrix instantiated with the witness. -/
theorem PRA_exists_witness_of_openDisjunction {n : ℕ} (φ : Semisentence language (n+1))
    (hOpen : φ.Open) (fallback : Code n) (ws : List (Code n))
    (hEither : UniversalAxiom ⊢ (∀⁰* openMatrixList φ fallback ws)) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* openMatrixAt φ c) := by
  obtain ⟨p, _, hp⟩ := PRAOpenFormulaCoverage.parseFormula_open φ hOpen
  subst φ
  rw [openMatrixList_asFormula] at hEither
  obtain ⟨c,hPR,hc⟩ := PRA_exists_witness_of_matrixDisjunction p fallback ws hEither
  exact ⟨c,hPR,hc⟩

end DiophantineConsistency.PRAHerbrandSelection
