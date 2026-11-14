import DiophantineConsistency.PRATermCompilation
import DiophantineConsistency.PRAPrimitiveRecursionInduction
import DiophantineConsistency.PRAWitnessExpBounds

/-! A concrete primitive-recursive code for iterating the arithmetic qVec
numerical majorant. Its recurrence holds in every candidate-PRA model; no
substitution-stage bound is asserted here. -/
set_option autoImplicit false
namespace PA196PRAQVecTower
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRATermCompilation PRAPrimitiveRecursionInduction PRAWitnessExpBounds

/-- For arguments `(iteration, current, initial)`, apply the majorant
`2^((current + 12) * 2^(22*current + 22))` to the current value. -/
noncomputable def stepTerm : TermN 3 :=
  expBound2 ‘#1 + 8 + 4’ ‘22 * #1 + 22’
noncomputable def stepCode : Code 3 := compileTerm stepTerm
/-- Arguments are the iteration count and the initial value. -/
noncomputable def towerCode : Code 2 := iterateCode (.proj 0) stepCode

theorem towerCode_primrec : Primrec (eval towerCode) := eval_primrec _

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

noncomputable def tower (n seed : M) : M := Structure.func (L := language) towerCode ![n, seed]

theorem tower_zero (seed : M) : tower 0 seed = seed := by
  have h := modelBase (M := M) (Code.proj (0 : Fin 1)) stepCode ![seed]
  change tower 0 seed = Structure.func (L := language) (Code.proj (0 : Fin 1)) ![seed] at h
  simpa [modelProjection] using h

theorem tower_succ (n seed : M) :
    tower (n + 1) seed =
      stepTerm.val ![n, tower n seed, seed] Empty.elim := by
  have h := modelStep (M := M) (Code.proj (0 : Fin 1)) stepCode ![n, seed]
  change tower (Structure.func (L := language) Code.succ (fun _ => n)) seed =
    Structure.func (L := language) stepCode ![n, tower n seed, seed] at h
  have hs : Structure.func (L := language) Code.succ (fun _ => n) = n + 1 := by
    symm
    exact modelAddOne n
  rw [hs] at h
  rw [h, stepCode, modelCompile]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
/-- The step term evaluates to the intended double-exponential expression in
every candidate-PRA model. Its arguments remain explicit arithmetic terms. -/
theorem stepTerm_eval (v : Fin 3 → M) :
    stepTerm.val v Empty.elim = PRAHistoryTruncation.expF
      ((‘#1 + 8 + 4’ : ArithmeticSemiterm Empty 3).val v Empty.elim *
        PRAHistoryTruncation.expF
          ((‘22 * #1 + 22’ : ArithmeticSemiterm Empty 3).val v Empty.elim)) :=
  val_expBound2 _ _ v

end models
#print axioms towerCode_primrec
#print axioms tower_zero
#print axioms tower_succ
#print axioms stepTerm_eval
end PA196PRAQVecTower
