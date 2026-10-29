import DiophantineConsistency.PRABoundedSearchFreeze
import DiophantineConsistency.PRAEqualityCode

/-! A primitive-recursive bit for a bounded universal predicate. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSearchUniversal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAQOrder
  PRAOpenFormulaCompiler PRABooleanOps PRAEqualityCode PRABoundedSearchCode PRABoundedSearchInvariant
  PRABoundedSearchBound PRABoundedSearchFreeze PRAPeanoMinusOrderAlgebra PRAPeanoMinusOrderBasic

def universalCode {n : ℕ} (good : Code (n+1)) : Code (n+1) :=
  .comp equalityCode (.cons (searchCode good) (.cons (.proj 0) (.nil (n+1))))

theorem universalCode_primrec {n : ℕ} (good : Code (n+1)) : Primrec (eval (universalCode good)) :=
  eval_primrec (universalCode good)

def boundedFormula {n : ℕ} (good : Code (n+1)) : Semisentence language (n+1) :=
  ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1])] 
    (Semiformula.nrel Language.ORing.Rel.eq
      ![applyCode good (Fin.cases (.bvar 0) (fun i : Fin n => .bvar i.succ.succ)),
        applyCode (Code.zero 0) Fin.elim0])

def universalCorrectSentence {n : ℕ} (good : Code (n+1)) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
    ![applyCode (universalCode good) (vars (n+1)), applyCode oneCode Fin.elim0]) 🡘 boundedFormula good)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSearchUniversal {n : ℕ} (good : Code (n+1)) (bound : M) (e : ℕ → M) :
    let params := fun i : Fin n => e i.val
    let find := fun x => Structure.func (L := language) (searchCode good) (Fin.cases x params)
    let g := fun x => Structure.func (L := language) good (Fin.cases x params)
    find bound = bound ↔ ∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,bound] →
      g x ≠ Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let params : Fin n → M := fun i => e i.val
  let find : M → M := fun x => Structure.func (L := language) (searchCode good) (Fin.cases x params)
  let g : M → M := fun x => Structure.func (L := language) good (Fin.cases x params)
  change find bound = bound ↔ ∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,bound] → g x ≠ z
  constructor
  · intro hbound x hx hbad
    obtain ⟨c,hc⟩ := (modelLtWitness x bound).mp hx
    have hf : g (find x) = z := modelSearchFindsBad good x e hbad
    have hs := modelSearchFreeze good x (s c) e hf
    change find (Structure.func (L := language) addCode ![x,s c]) = find x at hs
    rw [hc] at hs
    have heq : find x = bound := hs.symm.trans hbound
    have hle := modelSearchBound good x e
    change Structure.rel (L := language) Language.ORing.Rel.lt ![find x,x] ∨ find x = x at hle
    rcases hle with hlt | heq2
    · rw [heq] at hlt
      have hcirc := modelLtTrans bound x bound hlt hx
      exact modelLtIrrefl bound hcirc
    · rw [heq] at heq2
      subst x
      exact modelLtIrrefl bound hx
  · intro hgood
    have hcandidate := modelSearchCandidateInvariant good bound e
    change g (find bound) = z ∨ find bound = bound at hcandidate
    rcases hcandidate with hbad | heq
    · have hle := modelSearchBound good bound e
      change Structure.rel (L := language) Language.ORing.Rel.lt ![find bound,bound] ∨ find bound = bound at hle
      rcases hle with hlt | heq
      · exact False.elim ((hgood (find bound) hlt) hbad)
      · exact heq
    · exact heq

theorem modelUniversalCode {n : ℕ} (good : Code (n+1)) (bound : M) (e : ℕ → M) :
    let params := fun i : Fin n => e i.val
    let value := Structure.func (L := language) (universalCode good) (Fin.cases bound params)
    IsBit value ∧
      (value = Structure.func (L := language) oneCode Fin.elim0 ↔
        ∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,bound] →
          Structure.func (L := language) good (Fin.cases x params) ≠
            Structure.func (L := language) (Code.zero 0) Fin.elim0) := by
  let params : Fin n → M := fun i => e i.val
  let args : Fin (n+1) → M := Fin.cases bound params
  have hv : Structure.func (L := language) (universalCode good) args =
      Structure.func (L := language) equalityCode
        ![Structure.func (L := language) (searchCode good) args,bound] := by
    rw [universalCode, modelComposition]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      exact modelProjection 0 args
  change IsBit (Structure.func (L := language) (universalCode good) args) ∧
    (Structure.func (L := language) (universalCode good) args = Structure.func (L := language) oneCode Fin.elim0 ↔
      ∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,bound] →
        Structure.func (L := language) good (Fin.cases x params) ≠
          Structure.func (L := language) (Code.zero 0) Fin.elim0)
  rw [hv]
  have hc := modelEqualityCode (Structure.func (L := language) (searchCode good) args) bound
  exact ⟨hc.1, hc.2.trans (modelSearchUniversal good bound e)⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelBoundedFormula {n : ℕ} (good : Code (n+1)) (bound : M) (params : Fin n → M) :
    (boundedFormula good).Eval (Fin.cases bound params) Empty.elim ↔
      ∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,bound] →
        Structure.func (L := language) good (Fin.cases x params) ≠
          Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  simp only [boundedFormula, Semiformula.eval_ball, Semiformula.eval_rel, Semiformula.eval_nrel, eqRel]
  simp [applyCode, Semiterm.val_func]

theorem modelUniversalCorrectSentence {n : ℕ} (good : Code (n+1)) :
    M↓[language] ⊧ universalCorrectSentence good := by
  simp only [models_iff, universalCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  have hc := modelUniversalCode good (e 0) (fun i => if h : i < n then e ⟨i+1, by omega⟩ else e 0)
  -- The environment used by `modelUniversalCode` enumerates the tail of `e`.
  have hp : (fun i : Fin n => (if h : i.val < n then e ⟨i.val+1, by omega⟩ else e 0)) =
      (fun i : Fin n => e i.succ) := by
    funext i
    simp [i.isLt]
  rw [hp] at hc
  have he : Fin.cases (e 0) (fun i : Fin n => e i.succ) = e := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [he] at hc
  have hb := modelBoundedFormula good (e 0) (fun i : Fin n => e i.succ)
  rw [he] at hb
  -- Convert both sides of the displayed sentence to those model statements.
  simpa [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, vars] using (hc.2.trans hb.symm)

end models

theorem PRA_proves_universalCorrectSentence {n : ℕ} (good : Code (n+1)) :
    PRA ⊢ universalCorrectSentence good := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelUniversalCorrectSentence good

end DiophantineConsistency.PRABoundedSearchUniversal
