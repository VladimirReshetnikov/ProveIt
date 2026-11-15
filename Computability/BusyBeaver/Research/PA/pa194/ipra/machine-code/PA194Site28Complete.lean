import PA194Site28OutputFile
import PA194Site28SeedRoundTrip
import PA194Site28FinishReturn
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28Complete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Site28SeedTailRoundTrip PA194Site28SeedOutput PA194Site28SeedRoundTrip PA194Site28FinishReturn PA194Site28OutputFile PA194Site28CarryCodes PA194CarryFile PA194ReturnFile PA194UnaryRuns PA194ZeroRuns PA194StateOne PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

def seedOut (spare : M) : M := F block ![spare,F block ![(1 : M),modelNumeral M PA194StartupSourceFrame.seedTail]]
def seedRun (spare x : M) : M :=
  let e := PA194Site28SeedTailRoundTrip.ext spare
  let v := e ⟨25,by decide⟩
  let vals : Fin 26 → M := fun i => e i.castSucc
  F PA194Stepper.stepper ![F (PA194CarryFile.costCode 25) vals,
    F PA194Stepper.stepper ![modelNumeral M 2+((v+1)+1),
      F PA194Stepper.stepper ![modelNumeral M 3,
        F PA194Stepper.stepper ![(1 : M)+(v+1),
          F PA194Stepper.stepper ![F (timeCode 25) e,x]]]]]

def finishP (args : Fin 11 → M) : M :=
  let es := PA194Site28FinishReturn.rest args
  let vals : Fin 8 → M := fun i => es i.castSucc
  let out := F (returnCode 7) (Fin.cases (seedOut (args 9)) vals)
  let w1 := F ones ![args 8+1,(1 : M)+out+out]
  F ones ![args 2,(1 : M)+(w1+w1)+(w1+w1)]

def finishRun (k : M) (args : Fin 11 → M) (x : M) : M :=
  let es := PA194Site28FinishReturn.rest args
  let vals : Fin 8 → M := fun i => es i.castSucc
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+rc),
    F PA194Stepper.stepper ![(1 : M),
      F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
        F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![(k+1)+1,
              F PA194Stepper.stepper ![(args 2+1)+1,
                F PA194Stepper.stepper ![((args 8+1)+1)+1,
                  F PA194Stepper.stepper ![F (PA194CarryFile.costCode 7) vals,x]]]]]]]]]

def frame (site : Nat) (padding : M) (args : Fin 11 → M) : M :=
  let f := F sourceFileCode args
  F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
    PA194Path27Header.modelWord (PA194SourceProgram.path site) (F zeros ![padding,(1 : M)+(f+f)])]]

theorem complete (k : M) (args : Fin 11 → M)
    (htail : args 10 = modelNumeral M PA194StartupSourceFrame.seedTail) :
    finishRun k args (seedRun (args 9) (F PA194Stepper.stepper ![rootClock k args,frame 28 ((k+1)+1) args])) =
      frame 29 (k+1) (updated args) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let f := F sourceFileCode args
  let e := PA194Site28SeedTailRoundTrip.ext (args 9)
  let v := e ⟨25,by decide⟩
  let l := marked k args
  let s := ((1 : M)+1)+1
  let q := s+s
  let w := F ones ![v,(1 : M)+q+q]
  let t := w+w
  let vals : Fin 26 → M := fun i => e i.castSucc
  let out := F (PA194ReturnFile.returnCode 25) (Fin.cases t vals)
  have hseed := PA194Site28SeedRoundTrip.rootToSeedReturn k args htail
  change seedRun (args 9) (F PA194Stepper.stepper ![rootClock k args,frame 28 ((k+1)+1) args]) =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),out+out+1]] at hseed
  have hfile := PA194Site28SeedOutput.seedReturnFile (M := M) (args 9)
  change out = seedOut (args 9) at hfile
  rw [hfile] at hseed
  have hfinish := PA194Site28FinishReturn.finishReturn (M := M) k args (seedOut (args 9))
  change finishRun k args (F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
    seedOut (args 9)+seedOut (args 9)+1]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),PA194Path27Header.modelWord (PA194SourceProgram.path 29)
      (F zeros ![k+1,(1 : M)+(finishP args+finishP args)+(finishP args+finishP args)])]] at hfinish
  have hout := PA194Site28OutputFile.outputFile (M := M) args
  change F sourceFileCode (updated args) = finishP args+finishP args at hout
  rw [←hout] at hfinish
  have hsum : (1 : M)+(F sourceFileCode (updated args))+(F sourceFileCode (updated args)) =
      (1 : M)+((F sourceFileCode (updated args))+(F sourceFileCode (updated args))) := by rw [add_assoc]
  rw [hsum] at hfinish
  change finishRun k args (F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
    seedOut (args 9)+seedOut (args 9)+1]]) = frame 29 (k+1) (updated args) at hfinish
  exact (congrArg (finishRun k args) hseed).trans hfinish
#print axioms complete
end models
end PA194Site28Complete
