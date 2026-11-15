import PA194Site28Complete
import PA194Site28DynamicOutput
import PA194OneSpareFileRoundTrip
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194Site28DynamicComplete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Site28SeedRoundTrip PA194Site28FinishReturn PA194Site28CarryCodes PA194CarryFile PA194ReturnFile PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194OneSpareReturn PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def tailOut (count spare : M) : M := F block ![spare,F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]]
def tailRun (count spare x : M) : M :=
  F PA194Stepper.stepper ![(spare+1)+1,
    F PA194Stepper.stepper ![(count+count)+count,
      F PA194Stepper.stepper ![modelNumeral M 2,
        F PA194Stepper.stepper ![modelNumeral M 3,
          F PA194Stepper.stepper ![(count+count)+count,
            F PA194Stepper.stepper ![(1 : M)+(spare+1),x]]]]]]
def finishP (count : M) (args : Fin 11 → M) : M :=
  let es := PA194Site28FinishReturn.rest args
  let vals : Fin 8 → M := fun i => es i.castSucc
  let out := F (returnCode 7) (Fin.cases (tailOut count (args 9)) vals)
  let w1 := F ones ![args 8+1,(1 : M)+out+out]
  F ones ![args 2,(1 : M)+(w1+w1)+(w1+w1)]
theorem complete (k count : M) (args : Fin 11 → M)
    (htail : args 10 = F repeatOutput ![count,(0 : M)]) :
    PA194Site28Complete.finishRun k args (tailRun count (args 9) (F PA194Stepper.stepper ![rootClock k args,PA194Site28Complete.frame 28 ((k+1)+1) args])) =
      PA194Site28Complete.frame 29 (k+1) (PA194Site28DynamicOutput.updated args count) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let l := marked k args
  have hroot := rootToState3 k args
  dsimp only at hroot
  change F PA194Stepper.stepper ![rootClock k args,PA194Site28Complete.frame 28 ((k+1)+1) args] =
    F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![args 9+1,args 10]]] at hroot
  rw [htail] at hroot
  have hret := PA194OneSpareFileRoundTrip.roundTrip count (args 9) l (markedOdd k args)
  dsimp only at hret
  change tailRun count (args 9) (F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![args 9+1,F repeatOutput ![count,(0 : M)]]]]) =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),tailOut count (args 9)+tailOut count (args 9)+1]] at hret
  have hseed := (congrArg (tailRun count (args 9)) hroot).trans hret
  have hfinish := PA194Site28FinishReturn.finishReturn (M := M) k args (tailOut count (args 9))
  change PA194Site28Complete.finishRun k args (F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
    tailOut count (args 9)+tailOut count (args 9)+1]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),PA194Path27Header.modelWord (PA194SourceProgram.path 29)
      (F zeros ![k+1,(1 : M)+(finishP count args+finishP count args)+(finishP count args+finishP count args)])]] at hfinish
  have hout := PA194Site28DynamicOutput.outputFile (M := M) args count
  change F sourceFileCode (PA194Site28DynamicOutput.updated args count) = finishP count args+finishP count args at hout
  rw [←hout] at hfinish
  have hsum : (1 : M)+(F sourceFileCode (PA194Site28DynamicOutput.updated args count))+(F sourceFileCode (PA194Site28DynamicOutput.updated args count)) =
      (1 : M)+((F sourceFileCode (PA194Site28DynamicOutput.updated args count))+(F sourceFileCode (PA194Site28DynamicOutput.updated args count))) := by rw [add_assoc]
  rw [hsum] at hfinish
  change PA194Site28Complete.finishRun k args (F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
    tailOut count (args 9)+tailOut count (args 9)+1]]) = PA194Site28Complete.frame 29 (k+1) (PA194Site28DynamicOutput.updated args count) at hfinish
  exact (congrArg (PA194Site28Complete.finishRun k args) hseed).trans hfinish
#print axioms complete
end models
end PA194Site28DynamicComplete
