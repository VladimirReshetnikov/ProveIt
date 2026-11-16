import PA194MarkerReturnCell
import PA194UnaryRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnThree
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194MarkerReturnCell PA194UnaryRuns PA194StateOne PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnThree (k v0 v1 c out : M) :
    let d := c+c
    let l0 := F ones ![k,d+d]
    let l1 := l0+l0+1
    let l2 := l1+l1+1
    let l3 := l2+l2
    let l4 := F ones ![v0+1,l3]
    let l5 := l4+l4
    let left := F ones ![v1,l5]
    let a1 := F ones ![v1,(1 : M)+out+out]
    let a2 := F ones ![v0,(1 : M)+(a1+a1)+(a1+a1)]
    let a3 := F ones ![k+1,(1 : M)+(a2+a2)+(a2+a2)]
    let time := (((v1+1)+1)+((v0+1)+1))+(((k+1)+1)+1)
    F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 17,
      F pairCode ![left,(1 : M)+out+out]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![c,(a3+a3)+(a3+a3)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let d := c+c
  let l0 := F ones ![k,d+d]
  let l1 := l0+l0+1
  let l2 := l1+l1+1
  let l3 := l2+l2
  let l4 := F ones ![v0+1,l3]
  let l5 := l4+l4
  let z := F ones ![v0,l3]
  let a1 := F ones ![v1,(1 : M)+out+out]
  let a2 := F ones ![v0,(1 : M)+(a1+a1)+(a1+a1)]
  let a3 := F ones ![k+1,(1 : M)+(a2+a2)+(a2+a2)]
  have h4 : l4 = z+z+1 := by
    dsimp only [l4,z]
    rw [show v0+1 = F Code.succ (fun _ => v0) from modelAddOne _,modelOnesSucc]
  have h4odd : F parityCode (fun _ => l4) = (1 : M) := by rw [h4,(modelOdd z).1]
  have h4half : F halfCode (fun _ => l4) = z := by rw [h4,(modelOdd z).2]
  have h1 := modelMarkerReturnCell ⟨1,by decide⟩ v1 l4 out
  dsimp only at h1
  rw [h4odd,h4half] at h1
  change F PA194Stepper.stepper ![(v1+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F ones ![v1,l4+l4],out+out+1]]] = F pairCode ![modelNumeral M 17,F pairCode ![z,(1 : M)+(a1+a1)+(a1+a1)]] at h1
  have h2 := modelMarkerReturnCell ⟨1,by decide⟩ v0 l2 (a1+a1)
  dsimp only at h2
  rw [(modelOdd l1).1,(modelOdd l1).2] at h2
  change F PA194Stepper.stepper ![(v0+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F ones ![v0,l2+l2],(a1+a1)+(a1+a1)+1]]] = F pairCode ![modelNumeral M 17,F pairCode ![l1,(1 : M)+(a2+a2)+(a2+a2)]] at h2
  have h3 := modelMarkerReturnCell ⟨1,by decide⟩ (k+1) d (a2+a2)
  dsimp only at h3
  rw [(modelDouble c).1,(modelDouble c).2,zero_add] at h3
  change F PA194Stepper.stepper ![((k+1)+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F ones ![k+1,d+d],(a2+a2)+(a2+a2)+1]]] = F pairCode ![modelNumeral M 17,F pairCode ![c,(a3+a3)+(a3+a3)]] at h3
  have hleft : l1 = F ones ![k+1,d+d] := by
    dsimp only [l1,l0]
    rw [show k+1 = F Code.succ (fun _ => k) from modelAddOne _,modelOnesSucc]
  have eq1 : (1 : M)+out+out = out+out+1 := by simp only [add_assoc,add_comm,add_left_comm]
  have eq2 : (1 : M)+(a1+a1)+(a1+a1) = (a1+a1)+(a1+a1)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  have eq3 : (1 : M)+(a2+a2)+(a2+a2) = (a2+a2)+(a2+a2)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [eq1]
  change F PA194Stepper.stepper ![F addCode ![((v1+1)+1)+((v0+1)+1),((k+1)+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![(v1+1)+1,(v0+1)+1],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  rw [h1]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F pairCode ![modelNumeral M 17,F pairCode ![z,_]]]] = _
  rw [eq2,h2]
  change F PA194Stepper.stepper ![_,F pairCode ![modelNumeral M 17,F pairCode ![l1,_]]] = _
  rw [hleft,eq3,h3]
  simp only [a3,a2,a1,add_assoc,add_comm,add_left_comm]
#print axioms returnThree
end models
end PA194Site29ReturnThree
