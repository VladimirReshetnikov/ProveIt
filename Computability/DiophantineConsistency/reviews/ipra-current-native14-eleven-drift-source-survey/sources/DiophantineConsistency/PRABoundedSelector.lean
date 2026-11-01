import DiophantineConsistency.PRABoundedSearchUniversal
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSelector
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABoundedSearchCode
  PRABoundedSearchInvariant PRABoundedSearchBound PRABoundedSearchUniversal

def argsBound {n : ℕ} : Fin (n+1) → TermN (n+2) :=
  Fin.cases (#1) (fun i => .bvar i.succ.succ)
def argsWitness {n : ℕ} : Fin (n+1) → TermN (n+2) :=
  Fin.cases (#0) (fun i => .bvar i.succ.succ)
def foundTerm {n : ℕ} (good : Code (n+1)) : TermN (n+2) :=
  applyCode (searchCode good) argsBound
def goodWitnessTerm {n : ℕ} (good : Code (n+1)) : TermN (n+2) :=
  applyCode good argsWitness
def goodFoundTerm {n : ℕ} (good : Code (n+1)) : TermN (n+2) :=
  applyCode good (Fin.cases (foundTerm good) (fun i => .bvar i.succ.succ))
def zeroTerm {n : ℕ} : TermN (n+2) := applyCode (.zero 0) Fin.elim0
def matrix {n : ℕ} (good : Code (n+1)) : Semisentence language (n+2) :=
  ((.rel .lt ![#0,#1]) ⋏ (.rel .eq ![goodWitnessTerm good,zeroTerm])) 🡒
  ((.rel .lt ![foundTerm good,#1]) ⋏ (.rel .eq ![goodFoundTerm good,zeroTerm]))
def sentence {n : ℕ} (good : Code (n+1)) : Sentence language := ∀⁰* matrix good

theorem matrix_open {n : ℕ} (good : Code (n+1)) : (matrix good).Open := by simp [matrix, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSelector {n : ℕ} (good : Code (n+1)) (bound witness : M) (e : ℕ → M)
    (hbound : Structure.rel (L := language) Language.ORing.Rel.lt ![witness,bound])
    (hgood : Structure.func (L := language) good (Fin.cases witness (fun i : Fin n => e i.val)) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0) :
    let found := Structure.func (L := language) (searchCode good) (Fin.cases bound (fun i : Fin n => e i.val))
    Structure.rel (L := language) Language.ORing.Rel.lt ![found,bound] ∧
      Structure.func (L := language) good (Fin.cases found (fun i : Fin n => e i.val)) =
        Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have hne : Structure.func (L := language) (searchCode good) (Fin.cases bound (fun i : Fin n => e i.val)) ≠ bound := by
    intro he
    exact ((modelSearchUniversal good bound e).mp he witness hbound) hgood
  exact ⟨(modelSearchBound good bound e).resolve_right hne,
    (modelSearchCandidateInvariant good bound e).resolve_right hne⟩
theorem modelSentence {n : ℕ} (good : Code (n+1)) : M↓[language] ⊧ sentence good := by
  simp only [models_iff, sentence, Semiformula.eval_allClosure]
  intro v
  simp only [matrix, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_rel, PRAAddOne.eqRel]
  have hz : (Semiterm.val v Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN (n+2))) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [PRAAddOne.val_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    goodWitnessTerm, goodFoundTerm, foundTerm, zeroTerm, applyCode, Semiterm.val_func, Semiterm.val_bvar, hz]
  let params : Fin n → M := fun i => v i.succ.succ
  let e : ℕ → M := fun j => if hj : j < n then v ⟨j+2, by omega⟩ else v 0
  have he : (fun i : Fin n => e i.val) = params := by
    funext i
    simp only [e, dif_pos i.isLt, params]
    congr 1
  have hw : (Semiterm.val v Empty.elim ∘ (argsWitness : Fin (n+1) → TermN (n+2))) = Fin.cases (v 0) params := by
    funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have hb : (Semiterm.val v Empty.elim ∘ (argsBound : Fin (n+1) → TermN (n+2))) = Fin.cases (v 1) params := by
    funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have hf : (Semiterm.val v Empty.elim ∘ fun i =>
      Fin.cases (Semiterm.func (searchCode good) argsBound) (fun i => .bvar i.succ.succ) i) =
      Fin.cases (Structure.func (L := language) (searchCode good) (Fin.cases (v 1) params)) params := by
    funext i; cases i using Fin.cases with
    | zero =>
      change Semiterm.val v Empty.elim (Semiterm.func (searchCode good) argsBound) = _
      rw [Semiterm.val_func, hb, Fin.cases_zero]
    | succ i => rfl
  rw [hw,hb,hf]
  change (Structure.rel (L := language) Language.ORing.Rel.lt ![v 0,v 1] ∧
    Structure.func (L := language) good (Fin.cases (v 0) params) = Structure.func (L := language) (Code.zero 0) Fin.elim0) →
    (Structure.rel (L := language) Language.ORing.Rel.lt ![Structure.func (L := language) (searchCode good) (Fin.cases (v 1) params),v 1] ∧
      Structure.func (L := language) good (Fin.cases (Structure.func (L := language) (searchCode good) (Fin.cases (v 1) params)) params) =
        Structure.func (L := language) (Code.zero 0) Fin.elim0)
  intro h
  have hs := modelSelector good (v 1) (v 0) e h.1 (by simpa only [he] using h.2)
  simpa only [he] using hs
end models

theorem PRA_proves_selector {n : ℕ} (good : Code (n+1)) : PRA ⊢ sentence good := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence good
end DiophantineConsistency.PRABoundedSelector
