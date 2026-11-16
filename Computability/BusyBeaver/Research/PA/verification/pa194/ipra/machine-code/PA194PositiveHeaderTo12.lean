import PA194SixScanInvariant
import PA194IncrementTail
import PA194LeftOneWriteOne
import PA194SeedHeaderTo21
import PA194RightRows
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194PositiveHeaderTo12
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194SixScanInvariant PA194IncrementTail PA194LeftOneWriteOne
open PA194SeedHeaderTo21 PA194RightRows PA194BinaryDouble PA194UnaryRuns BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem boundaryTo12 (j r : M) :
    let j1 := j+j
    let j2 := j1+j1
    let j3 := j2+j2
    let w := r+r+1
    F PA194Stepper.stepper ![modelNumeral M 4,F pairCode ![modelNumeral M 6,F pairCode ![j3,w]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let j1 := j+j
  let j2 := j1+j1
  let w := r+r+1
  have h6 := leftOneWriteOne 6 6 (by decide) (by decide +kernel) (j2+j2) r
  rw [(modelDouble j2).1,(modelDouble j2).2,zero_add] at h6
  have h6' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 6,F pairCode ![j2+j2,w]]) =
      F pairCode ![modelNumeral M 6,F pairCode ![j2,w+w]] := by
    convert h6 using 1 <;> dsimp [w] <;> simp only [add_assoc,add_comm,add_left_comm]
  have he6 := rowEvenLeft (M := M) 6 7 (by decide) (by decide +kernel)
  have he7 := rowEvenLeft (M := M) 7 9 (by decide) (by decide +kernel)
  have h9 := rightZero (M := M) 9 1 12 (by decide) (by decide +kernel)
  simp only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] at h9
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 3),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h6',he6,he7,h9]

theorem positiveHeaderTo12 (k j file : M) :
    let j1 := j+j
    let j2 := j1+j1
    let j3 := j2+j2
    let scan := F ones ![k,j3]
    let a := scan+scan+1
    let p := (file+file)+(file+file)+1
    let w := F ones ![k+1,p]
    F PA194Stepper.stepper ![(modelNumeral M 2+k)+modelNumeral M 4,
      F pairCode ![modelNumeral M 6,F pairCode ![a+a+1,file+file]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let j1 := j+j
  let j2 := j1+j1
  let j3 := j2+j2
  let scan := F ones ![k,j3]
  let a := scan+scan+1
  let p := (file+file)+(file+file)+1
  let w0 := F ones ![k,p]
  have hw : F ones ![k+1,p] = w0+w0+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],p] = _
    rw [modelAddOne,modelOnesSucc]
  have h6 := packedSix a file
  have h7 := leftOneWriteOne 7 6 (by decide) (by decide +kernel) (scan+scan+1) (file+file)
  rw [(modelOdd scan).1,(modelOdd scan).2] at h7
  have h7' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 7,F pairCode ![scan+scan+1,(file+file)+(file+file)+1]]) =
      F pairCode ![modelNumeral M 6,F pairCode ![scan,p+p+1]] := by
    convert h7 using 1 <;> dsimp [p] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h2 : F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 6,
      F pairCode ![a+a+1,file+file]]] =
      F pairCode ![modelNumeral M 6,F pairCode ![scan,p+p+1]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h6,h7']
  have hs := modelFullScan k j3 p
  have h4 := boundaryTo12 j w0
  dsimp only at h4
  rw [hw] at hs ⊢
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2+k,modelNumeral M 4],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 4,F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,k],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h2,hs,h4]
#print axioms positiveHeaderTo12
#print axioms boundaryTo12
end models
end PA194PositiveHeaderTo12
