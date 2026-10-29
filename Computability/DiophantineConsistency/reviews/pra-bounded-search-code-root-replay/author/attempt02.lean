import DiophantineConsistency.PRASelectCode

/-! A parameterized primitive-recursive candidate for first-counterexample search. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSearchCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRASelectCode

/-- In a recursion-step environment `[counter, previous, parameters...]`,
apply the supplied predicate code to `[previous, parameters...]`. -/
def goodAtPrevious {n : ℕ} (good : Code (n+1)) : Code (n+2) :=
  .comp good (.cons (.proj (1 : Fin (n+2)))
    (pack n (fun i => .proj i.succ.succ)))

def nextCounter {n : ℕ} : Code (n+2) :=
  .comp Code.succ (.cons (.proj (0 : Fin (n+2))) (.nil (n+2)))

/-- Keep the previous index when it is bad; otherwise advance to the next
counter. Correctness as least-counterexample search is a separate obligation. -/
def searchStep {n : ℕ} (good : Code (n+1)) : Code (n+2) :=
  selectAmong (goodAtPrevious good) nextCounter (.proj (1 : Fin (n+2)))

def searchCode {n : ℕ} (good : Code (n+1)) : Code (n+1) :=
  .prec (.zero n) (searchStep good)

theorem searchCode_primrec {n : ℕ} (good : Code (n+1)) : Primrec (eval (searchCode good)) :=
  eval_primrec (searchCode good)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelGoodAtPrevious {n : ℕ} (good : Code (n+1)) (e : Fin (n+2) → M) :
    Structure.func (L := language) (goodAtPrevious good) e =
      Structure.func (L := language) good (Fin.cases (e 1) (fun i => e i.succ.succ)) := by
  rw [goodAtPrevious, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 1 e
  · simp only [getCode, getCode_pack]
    exact modelProjection j.succ.succ e

theorem modelNextCounter {n : ℕ} (e : Fin (n+2) → M) :
    Structure.func (L := language) nextCounter e =
      Structure.func (L := language) Code.succ (fun _ => e 0) := by
  rw [nextCounter, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  exact modelProjection 0 e

theorem modelSearchStep {n : ℕ} (good : Code (n+1)) (e : Fin (n+2) → M) :
    Structure.func (L := language) (searchStep good) e =
      Structure.func (L := language) selectCode
        ![Structure.func (L := language) good (Fin.cases (e 1) (fun i => e i.succ.succ)),
          Structure.func (L := language) Code.succ (fun _ => e 0), e 1] := by
  rw [searchStep, modelSelectAmong, modelGoodAtPrevious, modelNextCounter, modelProjection]

theorem modelSearchZero {n : ℕ} (good : Code (n+1)) (e : Fin n → M) :
    Structure.func (L := language) (searchCode good)
      (Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) e) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (.zero n) (searchStep good) e
  exact h.trans (PRAMultiplication.modelZero e)

theorem modelSearchStepEquation {n : ℕ} (good : Code (n+1)) (e : Fin (n+1) → M) :
    Structure.func (L := language) (searchCode good)
      (Fin.cases (Structure.func (L := language) Code.succ (fun _ => e 0)) (fun i => e i.succ)) =
      Structure.func (L := language) (searchStep good)
        (Fin.cases (e 0) (Fin.cases (Structure.func (L := language) (searchCode good) e)
          (fun i => e i.succ))) := modelStep (.zero n) (searchStep good) e

end models
end DiophantineConsistency.PRABoundedSearchCode
