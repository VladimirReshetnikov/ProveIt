import PA194Site32HeaderPass
import PA194Site32SecondTo71
import PA194Site29ScanTo71
import PA194SecondHeaderFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32TwoPassesTo71
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site32SecondTo71 PA194Path27Header PA194Site29ScanTo71 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem twoPassesTo71 (k : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let b := F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)]
    let p := F ones ![v 0+1,b+b]
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let r := F ones ![k,t]
    let w := r+r+1
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let l := (a6+a6)+(a6+a6)
    let tail := F ones ![v 2+1,F (fileCode 7) (fun i => v i.succ.succ.succ)]
    let l0 := F ones ![k,l]
    let l1 := l0+l0+1
    let l2 := l1+l1+1
    let l3 := l2+l2
    let l4 := F ones ![v 0+1,l3]
    let l5 := l4+l4
    let l6 := F ones ![v 1+1,l5]
    let cscan := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
    let f := F sourceFileCode args
    let z := F zeros ![k,f+f+1]
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c := (((((k+1)+1)+1)+1)+((k+1)+1))
    let c12 := F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)]
    let firstClock := F addCode ![F addCode ![F addCode ![c12,modelNumeral M 2],c],F addCode ![modelNumeral M 3,modelNumeral M 3+rc]]
    let c13 := F addCode ![c12,(1 : M)]
    F PA194Stepper.stepper ![F addCode ![firstClock,F addCode ![c13,cscan]],
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 32) ((z+z)+(z+z))]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![l6+l6,tail]] := by
  dsimp only
  let v := physicalArgs args
  have hf : F (fileCode 9) (fun i => v i.succ) =
      (F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)])+
      (F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)]) := by
    rw [modelFileSucc,modelBlock]
    rfl
  have first := PA194Site32HeaderPass.firstPass k args
  dsimp only at first
  rw [hf] at first
  have second := PA194Site32SecondTo71.secondPassTo71 k args
  dsimp only at second
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c := (((((k+1)+1)+1)+1)+((k+1)+1))
  let c12 := F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)]
  let c0 := F addCode ![F addCode ![F addCode ![c12,modelNumeral M 2],c],F addCode ![modelNumeral M 3,modelNumeral M 3+rc]]
  let c13 := F addCode ![c12,(1 : M)]
  let cs := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
  change F PA194Stepper.stepper ![F addCode ![c0,F addCode ![c13,cs]],_] = _
  rw [PA194StepperCompose.modelStepperCompose,first]
  let b := F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)]
  let p := F ones ![v 0+1,b+b]
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  have hw : F ones ![k+1,t] = F ones ![k,t]+F ones ![k,t]+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],t] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hw]
  exact second
#print axioms twoPassesTo71
end models
end PA194Site32TwoPassesTo71
