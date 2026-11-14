import PA194MarkedFile
import PA194CarryFile
import PA194StepperCompose
set_option autoImplicit false
namespace PA194IncrementFront
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelSelectedAndCarry (n : Nat) (e : Fin (n+2) → M) (l : M) :
    F PA194Stepper.stepper ![(((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ),
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (markedFile n) e]]] =
    F pairCode ![(1 : M),F pairCode ![F (leftCode n)
      (Fin.cases (F ones ![e 0,(l+l)+(l+l)+1]) (fun i => e i.succ)), e (Fin.last (n+1))]] := by
  change F PA194Stepper.stepper ![F addCode ![((1 : M)+1)+e 0,F (costCode n) (fun i => e i.succ)],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelSelectedMarked,modelCarryFile]
  have hl : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
  rw [hl]
#print axioms modelSelectedAndCarry
end models
end PA194IncrementFront
