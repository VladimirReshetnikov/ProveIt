import PA194ScanInvariant
import PA194OnesCommute
import PA194RightRows
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ThirdPassTo4
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194ScanInvariant PA194StateOne PA194UnaryRuns
open PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem threeTo1 (l x : M) :
    let w := x+x+1
    let l1 := l+l+1
    let l2 := l1+l1+1
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 1,
      F pairCode ![l,((w+w)+(w+w))+1]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![l2+l2,x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelNumeralOne]
  have h1 := rightOne (M := M) 1 1 1 (by decide) (by decide +kernel)
  have h2 := rightZero (M := M) 1 1 3 (by decide) (by decide +kernel)
  have h3 := rightOne (M := M) 3 0 1 (by decide) (by decide +kernel)
  simp only [show modelNumeral M 0 = (0 : M) from rfl,show modelNumeral M 1 = (1 : M) from modelNumeralOne,add_zero] at h1 h2 h3
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [h1,h2,h3]

theorem twoTo4 (l b : M) :
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 1,
      F pairCode ![l,(b+b)+(b+b)]]] =
    F pairCode ![modelNumeral M 4,F pairCode ![(l+l+1)+(l+l+1),b]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelNumeralOne]
  have h1 := rightZero (M := M) 1 1 3 (by decide) (by decide +kernel)
  have h3 := rightZero (M := M) 3 0 4 (by decide) (by decide +kernel)
  simp only [show modelNumeral M 0 = (0 : M) from rfl,show modelNumeral M 1 = (1 : M) from modelNumeralOne,add_zero] at h1 h3
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [h1,h3]

theorem scanTo4 (l n b : M) :
    let c := (b+b)+(b+b)
    let x := F ones ![n,c]
    let w := x+x+1
    let l1 := l+l+1
    let l2 := l1+l1+1
    let a := F ones ![n,l2+l2]
    F PA194Stepper.stepper ![(modelNumeral M 3+n)+modelNumeral M 2,
      F pairCode ![modelNumeral M 1,F pairCode ![l,((w+w)+(w+w))+1]]] =
    F pairCode ![modelNumeral M 4,F pairCode ![(a+a+1)+(a+a+1),b]] := by
  dsimp only
  let c := (b+b)+(b+b)
  let x := F ones ![n,c]
  let l1 := l+l+1
  let l2 := l1+l1+1
  let a := F ones ![n,l2+l2]
  have h3 := threeTo1 l x
  dsimp only at h3
  have hscan := modelFullScan n (l2+l2) c
  have h2 := twoTo4 a b
  rw [modelNumeralOne] at h2
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3+n,modelNumeral M 2],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 2,F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,n],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h3,modelNumeralOne,hscan,h2]
#print axioms scanTo4
#print axioms threeTo1
#print axioms twoTo4
end models
end PA194ThirdPassTo4
