import PA194Site28DynamicComplete
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194Site28DynamicClock
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194RegisterPermutation PA194RegisterFile PA194Site28SeedRoundTrip PA194Site28Complete
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def clock (k count : M) (args : Fin 11 → M) : M :=
  let es := PA194Site28FinishReturn.rest args
  let vals : Fin 8 → M := fun i => es i.castSucc
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c := rootClock k args
  let c := c+((1 : M)+(args 9+1))
  let c := c+((count+count)+count)
  let c := c+modelNumeral M 3
  let c := c+modelNumeral M 2
  let c := c+((count+count)+count)
  let c := c+((args 9+1)+1)
  let c := c+F (PA194CarryFile.costCode 7) vals
  let c := c+(((args 8+1)+1)+1)
  let c := c+((args 2+1)+1)
  let c := c+((k+1)+1)
  let c := c+modelNumeral M 2
  let c := c+(((modelNumeral M 2+1)+k)+1)
  let c := c+(((1 : M)+k)+modelNumeral M 3)
  let c := c+(1 : M)
  c+(modelNumeral M 2+(modelNumeral M 3+rc))

theorem exactClock (k count : M) (args : Fin 11 → M)
    (htail : args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    F PA194Stepper.stepper ![clock k count args,frame 28 ((k+1)+1) args] =
      frame 29 (k+1) (PA194Site28DynamicOutput.updated args count) := by
  have hp := PA194Site28DynamicComplete.complete k count args htail
  dsimp only [PA194Site28DynamicComplete.tailRun, PA194Site28Complete.finishRun] at hp
  simp only [←PA194StepperCompose.modelStepperCompose] at hp
  exact hp
#print axioms exactClock
end models
end PA194Site28DynamicClock
