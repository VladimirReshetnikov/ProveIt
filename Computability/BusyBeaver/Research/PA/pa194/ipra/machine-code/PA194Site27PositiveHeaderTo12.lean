import PA194PositiveRewind
import PA194IncrementTail
import PA194SeedHeaderTo21
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27PositiveHeaderTo12
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194PositiveRewind PA194IncrementTail PA194SeedHeaderTo21 PA194RightRows PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem boundaryTo12 (j w : M) :
    let j1 := j+j
    let j2 := j1+j1
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 6,F pairCode ![j2,w+w]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,(w+w)+(w+w)]] := by
  dsimp only
  have h6 := rowEvenLeft (M := M) 6 7 (by decide) (by decide +kernel)
  have h7 := rowEvenLeft (M := M) 7 9 (by decide) (by decide +kernel)
  have h9 := rightZero (M := M) 9 1 12 (by decide) (by decide +kernel)
  simp only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] at h9
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h6,h7,h9]

theorem headerTo12 (k j file : M) :
    let j1 := j+j
    let base := j1+j1
    let before := F ones ![k+1,base+base]
    let w := F ones ![k+1,(file+file)+(file+file)+1]
    F PA194Stepper.stepper ![((1 : M)+((k+1)+1))+modelNumeral M 3,
      F pairCode ![modelNumeral M 6,F pairCode ![before+before+1,file+file]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,(w+w)+(w+w)]] := by
  dsimp only
  let j1 := j+j
  let base := j1+j1
  let before := F ones ![k+1,base+base]
  let w := F ones ![k+1,(file+file)+(file+file)+1]
  have h6 := packedSix before file
  have hr := positiveRewind (k+1) base (file+file)
  dsimp only at hr
  have h3 := boundaryTo12 j w
  dsimp only at h3
  change F PA194Stepper.stepper ![F addCode ![(1 : M)+((k+1)+1),modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 3,F PA194Stepper.stepper ![F addCode ![(1 : M),(k+1)+1],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  have h1 : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 6,
      F pairCode ![before+before+1,file+file]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![before,(file+file)+(file+file)+1]] := by
    nth_rewrite 1 [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h6]
  rw [h1,hr,h3]
#print axioms boundaryTo12
#print axioms headerTo12
end models
end PA194Site27PositiveHeaderTo12
