import PA194AXModelSymbolic
import PA194AXResultExpressions

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PA194AXModelValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194TargetCantor PA194TargetLeaves PA194TargetGate PA194MachineStack
open PA194MachineProjections PA194DiagonalLink PA194ModelAXPlan
open PA194AXModelSymbolic

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

private theorem add_two_steps (a : M) : (a + 1) + 1 = a + 2 := by
  rw [add_assoc,one_add_one_eq_two]

private theorem add_three_steps (a : M) : (a + 2) + 1 = a + 3 := by
  rw [add_assoc,show (2 : M) + 1 = 3 by norm_num]

private theorem fixedProjections (p : M) :
    cantor (F fixedFirst ![p]) (F fixedSecond ![p]) = p := by
  rw [fixedFirst_model,fixedSecond_model,cantor_projections]

noncomputable def bodyValues (a : Fin 11 → M) : Fin 11 → M :=
  let field := F fixedSecond ![a 8]
  let d := a 4 + F fixedFirst ![field]
  let h := a 5 + F fixedFirst ![a 8]
  ![a 0,oldBundleValue h d (a 3),axStack d h (a 3) (a 4) (a 5) (a 1) (a 2),
    a 3,d,h,0,0,F fixedSecond ![field],a 9,a 10]

/-- Evaluate the certified symbolic expression in the same model as the
controller run. Its interpretation preserves the arbitrary stack base. -/
theorem body_evaluation (a : Fin 11 → M) (hx : a 6 = 0) (hy : a 7 = 0) :
    actions PA194AXSymbolic.core a = bodyValues a := by
  let field := F fixedSecond ![a 8]
  let y := F fixedFirst ![a 8]
  let x := F fixedFirst ![field]
  let suffix := F fixedSecond ![field]
  let env : Fin 6 → M := ![a 1,a 3,a 4,a 5,y,x]
  have hp : cantor y (cantor x suffix) = a 8 := by
    change cantor (F fixedFirst ![a 8]) (cantor (F fixedFirst ![field]) (F fixedSecond ![field])) = _
    rw [fixedProjections]
    exact fixedProjections _
  have hin : materialize env (a 2) suffix a PA194AXSymbolic.initial = a := by
    funext i
    fin_cases i <;> simp [materialize,PA194AXSymbolic.initial,env,value,stack,hx,hy,hp]
  calc
    actions PA194AXSymbolic.core a =
        actions PA194AXSymbolic.core (materialize env (a 2) suffix a PA194AXSymbolic.initial) :=
      congrArg _ hin.symm
    _ = materialize env (a 2) suffix a PA194AXSymbolic.result :=
      PA194AXModelSymbolic.run_sound _ _ _ PA194AXSymbolic.symbolic_run _ _ _ _
    _ = bodyValues a := by
      rw [PA194AXResultExpressions.expectedResult]
      simp [materialize,PA194AXResultExpressions.result,PA194AXResultExpressions.heads,
        PA194AXResultExpressions.bundle,PA194AXResultExpressions.membership,
        PA194AXResultExpressions.separationTail,PA194AXResultExpressions.separate,
        PA194AXResultExpressions.point,PA194AXResultExpressions.both,
        PA194AXResultExpressions.all,PA194AXResultExpressions.ex,PA194AXResultExpressions.mem,
        PA194AXResultExpressions.equal,PA194AXResultExpressions.neg,PA194AXResultExpressions.one,
        bodyValues,field,x,y,env,suffix,value,stack,oldBundleValue,memVacValue,separationTailValue,
        separationValue,pointValue,conjValue,axStack,diagonalValue,head6Value,head5Value,head4Value,
        head3Value,head2Value,head1Value,rho8Value,memValue,eqValue,exValue,allValue,negValue,
        add_two_steps,add_three_steps]

#print axioms body_evaluation
end models
end PA194AXModelValues
