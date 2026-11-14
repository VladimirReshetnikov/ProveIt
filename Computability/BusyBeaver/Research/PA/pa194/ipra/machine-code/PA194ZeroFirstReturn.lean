import PA194MarkDelimiter
import PA194FourteenComposition
import PA194HeaderController
import PA194SevenReturnController
import PA194FifteenExitComposition
import PA194ZeroRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroFirstReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194BinaryDouble PA194MarkDelimiter PA194FourteenComposition PA194HeaderController PA194StateOne
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ZeroRuns PA194SevenReturnController
open PA194FifteenExitComposition PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The zero-first-block branch reaches dense 15 with exact model tape halves. -/
theorem zeroToFifteen (a r : M) :
    let n := modelNumeral M 2
    let b := F block ![(0 : M),r+r]
    let l := a+a+1
    let z := F zeros ![(0 : M),F zeros ![n,l]+F zeros ![n,l]]
    F PA194Stepper.stepper ![modelNumeral M 2+(((n+1)+(0 : M))+1+1),
      F pairCode ![modelNumeral M 7,F pairCode ![a+a,b+b]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => F halfCode (fun _ => z)),
      F parityCode (fun _ => F halfCode (fun _ => z))+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let b := F block ![(0 : M),r+r]
  let l := a+a+1
  have hb : b+b = F zeros ![modelNumeral M 2,F ones ![(0 : M),r+r]+F ones ![(0 : M),r+r]+1] := by
    rw [modelOnesZero,zerosTwo]
    dsimp [b]
    rw [modelBlock,zero_add,←modelNumeralOne]
    rw [show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
    rw [show F Code.succ (fun _ => (0 : M)) = modelNumeral M 1 from rfl,modelNumeralOne]
  have hm := modelConnectedFifteen (modelNumeral M 2) (0 : M) l r
  dsimp only at hm
  rw [←hb] at hm
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,sevenToTwelve]
  exact hm
/-- Two zero reads return across the controller's trailing `01`. -/
theorem twoReturn (a r : M) :
    let l := a+a+1
    let t := (1 : M)+(r+r)+(r+r)
    F PA194Stepper.stepper ![modelNumeral M 2,
      F pairCode ![modelNumeral M 15,F pairCode ![l+l,t+t]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![a,((t+t)+(t+t))+((t+t)+(t+t))+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,modelPackedReturn]
  simp only [(modelDouble _).1,(modelDouble _).2,zero_add]
  rw [modelPackedReturn]
  simp only [(modelOdd _).1,(modelOdd _).2]
  ac_rfl
/-- Simplified state-15 output for the zero block. -/
theorem zeroToFifteenSimple (a r : M) :
    let b := F block ![(0 : M),r+r]
    let l := a+a+1
    let t := (1 : M)+(r+r)+(r+r)
    F PA194Stepper.stepper ![modelNumeral M 2+(((modelNumeral M 2+1)+(0 : M))+1+1),
      F pairCode ![modelNumeral M 7,F pairCode ![a+a,b+b]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![l+l,t+t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hm := zeroToFifteen (M := M) a r
  dsimp only at hm ⊢
  rw [modelZerosZero,zerosTwo] at hm
  simp only [(modelDouble _).1,(modelDouble _).2,zero_add] at hm
  have ht (x : M) : (1 : M)+(1 : M)+(x+x)+(x+x) = (1+x+x)+(1+x+x) := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [ht] at hm
  exact hm
/-- The zero block is crossed and the controller reaches its odd return cell. -/
theorem zeroToOddFifteen (a r : M) :
    let b := F block ![(0 : M),r+r]
    let t := (1 : M)+(r+r)+(r+r)
    F PA194Stepper.stepper ![(modelNumeral M 2+(((modelNumeral M 2+1)+(0 : M))+1+1))+modelNumeral M 2,
      F pairCode ![modelNumeral M 7,F pairCode ![a+a,b+b]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![a,((t+t)+(t+t))+((t+t)+(t+t))+1]] := by
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,zeroToFifteenSimple]
  exact twoReturn a r
#print axioms zeroToOddFifteen
#print axioms zeroToFifteenSimple
#print axioms twoReturn
#print axioms zeroToFifteen
end models
end PA194ZeroFirstReturn
