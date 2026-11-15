import PA194PositiveRewind
import PA194IncrementTail
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27PositiveCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194PositiveRewind PA194IncrementTail PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnCell (n l file : M) :
    let a := l+l+1
    let left := F ones ![n,a+a]
    let r := file+file
    let next := F ones ![n,(r+r)+1]
    F PA194Stepper.stepper ![(1 : M)+(n+1),F pairCode ![modelNumeral M 6,
      F pairCode ![left+left+1,file+file]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![a,next+next]] := by
  dsimp only
  let a := l+l+1
  let left := F ones ![n,a+a]
  let r := file+file
  have hstep := packedSix left file
  have hr := positiveRewind n a r
  dsimp only at hr
  change F PA194Stepper.stepper ![F addCode ![(1 : M),n+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  have h1 : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 6,
      F pairCode ![left+left+1,file+file]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![left,(file+file)+(file+file)+1]] := by
    nth_rewrite 1 [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,hstep]
  rw [h1,hr]
#print axioms returnCell
end models
end PA194Site27PositiveCell
