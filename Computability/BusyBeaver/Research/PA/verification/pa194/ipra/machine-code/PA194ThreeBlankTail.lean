import PA194IncrementTail
import PA194TailThree
import PA194TailFive
import PA194TailSeven
import PA194TailSix
import PA194CarryEntry
import PA194TailFour
import PA194Stepper
import PA194ZeroRuns
set_option autoImplicit false
namespace PA194ThreeBlankTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194CarryEntry PA194BinaryDouble PA194TailThree PA194TailFour PA194TailFive PA194TailSeven PA194TailSix PA194ZeroRuns PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelThreeBlankTail (l : M) :
    let c3 := ((1 : M)+1)+1
    let c6 := c3+c3
    let c13 := (c6+c6)+1
    F PA194Stepper.stepper ![TableDispatch.modelNumeral M 5,F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![l+l+1,(0 : M)]]] =
      F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,c13]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let c3 : M := (1+1)+1
  let c6 : M := c3+c3
  let c13 : M := (c6+c6)+1
  let x := l+l+1
  have h2 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![x,(0 : M)]]) =
      F pairCode ![TableDispatch.modelNumeral M 4,F pairCode ![x+x,(0 : M)]] := by
    simpa only [zero_add] using PA194IncrementTail.packedThree x (0 : M)
  have h3 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 4,F pairCode ![x+x,(0 : M)]]) =
      F pairCode ![TableDispatch.modelNumeral M 5,F pairCode ![(x+x)+(x+x)+1,(0 : M)]] := by
    simpa only [zero_add] using PA194IncrementTail.packedFour (x+x) (0 : M)
  have h4 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 5,F pairCode ![(x+x)+(x+x)+1,(0 : M)]]) =
      F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![x+x,c3]] := by
    simpa only [zero_add,c3] using PA194IncrementTail.packedFive (x+x) (0 : M)
  have h5 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![x+x,c3]]) =
      F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![x,c6]] := by
    simpa only [c3,c6] using PA194IncrementTail.packedSeven x (1 : M)
  have h6 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![x,c6]]) =
      F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,c13]] := by
    simpa only [x,c3,c6,c13] using PA194IncrementTail.packedSix l (((1 : M)+1)+1)
  have stepNum (k : Nat) (c : M) : F PA194Stepper.stepper ![TableDispatch.modelNumeral M (k+1),c] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![TableDispatch.modelNumeral M k,c]) := by
    rw [PA194FiniteControls.modelNumeralSucc]
    change F PA194Stepper.stepper ![F addCode ![TableDispatch.modelNumeral M k,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  repeat rw [stepNum]
  have hz : TableDispatch.modelNumeral M 0 = F (Code.zero 0) Fin.elim0 := rfl
  rw [hz]
  rw [PA194Stepper.modelStepperZero,h2,h3,h4,h5,h6]
#print axioms modelThreeBlankTail
end models
end PA194ThreeBlankTail
