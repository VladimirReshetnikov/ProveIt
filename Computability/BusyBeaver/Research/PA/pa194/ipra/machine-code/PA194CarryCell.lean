import PA194CarryEntry
import PA194ScanInvariant
import PA194StepperCompose
set_option autoImplicit false
namespace PA194CarryCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194UnaryRuns PA194CarryEntry PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelCarryCell (n l t : M) :
    let a := F ones ![n,t]
    F PA194Stepper.stepper ![((1 : M)+1)+n,F pairCode ![TableDispatch.modelNumeral M 1,
      F pairCode ![l,(a+a+1)+(a+a+1)]]] =
    F pairCode ![(1 : M),F pairCode ![F ones ![n,(l+l+1)+(l+l+1)],t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let a := F ones ![n,t]
  let c := F pairCode ![TableDispatch.modelNumeral M 1,F pairCode ![l,(a+a+1)+(a+a+1)]]
  have hs (v : M) : F PA194Stepper.stepper ![v+1,c] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![v,c]) := by
    change F PA194Stepper.stepper ![F addCode ![v,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have h0 : F PA194Stepper.stepper ![(0 : M),c] = c := PA194Stepper.modelStepperZero c
  have hstart : F PA194Stepper.stepper ![(1 : M)+1,c] =
      F pairCode ![(1 : M),F pairCode ![(l+l+1)+(l+l+1),a]] := by
    have hstart0 : F PA194Stepper.stepper ![((0 : M)+1)+1,c] =
        F pairCode ![(1 : M),F pairCode ![(l+l+1)+(l+l+1),a]] := by
      rw [hs,hs,h0]
      dsimp only [c]
      rw [modelPackedCarryOne,modelPackedCarryThree,modelNumeralOne]
    simpa only [zero_add] using hstart0
  change F PA194Stepper.stepper ![F addCode ![(1 : M)+1,n],c] = _
  rw [PA194StepperCompose.modelStepperCompose,hstart,PA194ScanInvariant.modelFullScan]
#print axioms modelCarryCell
end models
end PA194CarryCell
