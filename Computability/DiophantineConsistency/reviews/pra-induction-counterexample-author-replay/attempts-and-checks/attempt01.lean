import DiophantineConsistency.PRAPrimitiveRecursionInduction
import DiophantineConsistency.PRATermCompilation

/-! Defeat a fixed coded induction counterexample by primitive recursion. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAInductionCounterexample
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRAMultiplication
  PRAPrimitiveRecursionInduction

def fixedZeroStep {n : ℕ} (q : Code (n+3)) : Code (n+2) :=
  .comp q (.cons (.proj 0) (.cons (.proj 1) (.cons (.zero (n+2))
    (pack n (fun i => .proj i.succ.succ)))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelFixedZeroStep {n : ℕ} (q : Code (n+3)) (x y : M) (params : Fin n → M) :
    Structure.func (L := language) (fixedZeroStep q) (Fin.cases x (Fin.cases y params)) =
      Structure.func (L := language) q (Fin.cases x (Fin.cases y (Fin.cases
        (Structure.func (L := language) (Code.zero 0) Fin.elim0) params))) := by
  rw [fixedZeroStep, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 _
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 1 _
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact modelZero _
      · simp only [getCode, getCode_pack]
        exact modelProjection l.succ.succ _

/-- The coded analogue of the counterexample-defeat lemma: for each parameter
valuation, some triple defeats the proposed open induction counterexample. -/
theorem modelCounterexampleDefeat {n : ℕ} (pred : Code (n+2)) (base stop : Code n) (q : Code (n+3))
    (e : ℕ → M) :
    let params := fun i : Fin n => e i.val
    let zero := Structure.func (L := language) (Code.zero 0) Fin.elim0
    let one := Structure.func (L := language) oneCode Fin.elim0
    let p := fun x y => Structure.func (L := language) pred (Fin.cases x (Fin.cases y params)) = one
    let next := fun x y w => Structure.func (L := language) q (Fin.cases x (Fin.cases y (Fin.cases w params)))
    let target := Structure.func (L := language) stop params
    ∃ x y w, ¬(p zero (Structure.func (L := language) base params) ∧
      (p x y → p (Structure.func (L := language) Code.succ (fun _ => x)) (next x y w)) ∧ ¬p target w) := by
  let params : Fin n → M := fun i => e i.val
  let zero : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let one : M := Structure.func (L := language) oneCode Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let p : M → M → Prop := fun x y => Structure.func (L := language) pred (Fin.cases x (Fin.cases y params)) = one
  let next : M → M → M → M := fun x y w => Structure.func (L := language) q (Fin.cases x (Fin.cases y (Fin.cases w params)))
  let target : M := Structure.func (L := language) stop params
  change ∃ x y w, ¬(p zero (Structure.func (L := language) base params) ∧
    (p x y → p (s x) (next x y w)) ∧ ¬p target w)
  classical
  by_contra hn
  push Not at hn
  have hbase : p zero (Structure.func (L := language) base params) := (hn zero zero zero).1
  have hstep : ∀ x y, p x y → p (s x) (Structure.func (L := language) (fixedZeroStep q) (Fin.cases x (Fin.cases y params))) := by
    intro x y hxy
    rw [modelFixedZeroStep]
    exact (hn x y zero).2.1 hxy
  have hrec := modelRecursiveWitness pred base (fixedZeroStep q) e hbase hstep target
  let witness := Structure.func (L := language) (iterateCode base (fixedZeroStep q)) (Fin.cases target params)
  have hnot : ¬p target witness := (hn zero zero witness).2.2
  exact hnot hrec

end models
end DiophantineConsistency.PRAInductionCounterexample
