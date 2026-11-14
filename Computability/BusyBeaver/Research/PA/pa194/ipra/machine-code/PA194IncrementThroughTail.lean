import PA194IncrementFront
import PA194IncrementTail
set_option autoImplicit false
namespace PA194IncrementThroughTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194IncrementFront PA194IncrementTail
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelThroughTail (n : Nat) (e : Fin (n+2) → M) (l : M)
    (he : e (Fin.last (n+1)) = (0 : M)) :
    let left := F (leftCode n) (Fin.cases (F ones ![e 0,(l+l)+(l+l)+1]) (fun i => e i.succ))
    let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
    let c3 := ((1 : M)+1)+1
    let c13 := ((c3+c3)+(c3+c3))+1
    F PA194Stepper.stepper ![front+TableDispatch.modelNumeral M 6,
      F pairCode ![TableDispatch.modelNumeral M 2,F pairCode ![l,F (markedFile n) e]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![left,c13]] := by
  let front := (((1 : M)+1)+e 0)+F (costCode n) (fun i => e i.succ)
  let left := F (leftCode n) (Fin.cases (F ones ![e 0,(l+l)+(l+l)+1]) (fun i => e i.succ))
  change F PA194Stepper.stepper ![F addCode ![front,TableDispatch.modelNumeral M 6],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelSelectedAndCarry,he,modelAppendTail]
#print axioms modelThroughTail
end models
end PA194IncrementThroughTail
