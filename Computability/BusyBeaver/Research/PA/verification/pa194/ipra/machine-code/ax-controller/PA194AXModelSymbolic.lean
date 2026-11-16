import PA194ModelAXPlan
import PA194AXSymbolic
import PA194DiagonalLink

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PA194AXModelSymbolic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194TargetCantor PA194TargetLeaves PA194TargetGate PA194MachineStack
open PA194MachineProjections PA194DiagonalLink PA194ModelAXPlan
open M6.Source.AXSymbolic

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Evaluate a symbolic AX register expression in the arithmetic model. -/
noncomputable def value (v : Fin 6 → M) : Expr → M
  | .zero => 0
  | .atom i => v i
  | .succ a => value v a + 1
  | .add a b => value v a + value v b
  | .im a b => impValue (value v a) (value v b)

theorem value_plus (v : Fin 6 → M) (a b : Expr) :
    value v (plus a b) = value v a + value v b := by
  cases a <;> cases b <;> simp [value,plus]

noncomputable def stack (v : Fin 6 → M) (bottom : M) : List Expr → M
  | [] => bottom
  | e::es => cantor (value v e) (stack v bottom es)

/-- Only the command suffix and stack need a packed interpretation. The
registers outside the AX body are carried through in the extra vector. -/
noncomputable def materialize (v : Fin 6 → M) (bottom suffix : M)
    (extra : Fin 11 → M) (sym : Store) : Fin 11 → M :=
  ![extra 0, value v sym.t, stack v bottom sym.stack, value v sym.a,
    value v sym.d, value v sym.h, 0, 0, stack v suffix sym.fields, extra 9, extra 10]

private theorem numeral_cast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PA194FiniteControls.modelNumeralSucc, ih, Nat.cast_succ]

theorem exec_sound (op : Op) (sym next : Store) (he : exec op sym = some next)
    (v : Fin 6 → M) (bottom suffix : M) (extra : Fin 11 → M) :
    action op (materialize v bottom suffix extra sym) = materialize v bottom suffix extra next := by
  cases op <;> cases sym with
  | mk t a d h fields stk =>
    cases fields <;> cases stk <;>
      simp only [exec,Option.some.injEq] at he <;> cases he <;>
      funext i <;> fin_cases i <;>
        simp [action,materialize,value,stack,value_plus,PA194ModelMPPush.pushed,
          numeral_cast,impValue,fixedFirst_model,first_cantor,fixedSecond_model,second_cantor]

theorem run_sound (ops : List Op) (sym next : Store) (he : run ops sym = some next)
    (v : Fin 6 → M) (bottom suffix : M) (extra : Fin 11 → M) :
    actions ops (materialize v bottom suffix extra sym) = materialize v bottom suffix extra next := by
  induction ops generalizing sym with
  | nil =>
    simp only [run,Option.some.injEq] at he
    subst next
    rfl
  | cons op ops ih =>
    cases hx : exec op sym with
    | none => simp [run,hx] at he
    | some mid =>
      simp only [run,hx,Option.bind_some] at he
      rw [actions,exec_sound op sym mid hx]
      exact ih mid he

#print axioms exec_sound
#print axioms run_sound
end models
end PA194AXModelSymbolic
