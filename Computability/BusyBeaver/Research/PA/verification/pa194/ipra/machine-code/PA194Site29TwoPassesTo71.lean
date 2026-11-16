import PA194Site29HeaderPass
import PA194Site29SecondPassTo71
import PA194Site29SecondDispatch
import PA194Site29ScanTo71
import PA194SecondHeaderFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29TwoPassesTo71
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site29SecondDispatch PA194Site29ScanTo71 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
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
    let r2 := w+w
    let u0 := r2+r2+1
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a := a4+a4
    let bb := a+a+1
    let cc := bb+bb+1
    let d := cc+cc
    let l := d+d
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
    let z0 := z+z
    let z1 := z0+z0
    let z2 := z1+z1
    let z3 := z2+z2+1
    let z4 := z3+z3+1
    let z5 := z4+z4
    let z6 := z5+z5+1
    let z7 := z6+z6
    let z8 := z7+z7
    let z9 := z8+z8
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let firstClock := (modelNumeral M 19+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 7+rc)
    F PA194Stepper.stepper ![firstClock+(modelNumeral M 18+cscan),
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),z9+z9+1]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![l6+l6,tail]] := by
  dsimp only
  let v := physicalArgs args
  have hf : F (fileCode 9) (fun i => v i.succ) =
      (F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)])+
      (F ones ![v 1+1,F (fileCode 8) (fun i => v i.succ.succ)]) := by
    rw [modelFileSucc,modelBlock]
    rfl
  have shape := PA194SecondHeaderFile.sourceFirstPassShape k args
  dsimp only at shape
  rw [hf] at shape
  have first := PA194Site29HeaderPass.site29HeaderPass k args
  dsimp only at first
  rw [hf,shape.2] at first
  have second := PA194Site29SecondPassTo71.secondPassTo71 k args
  dsimp only at second
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c0 := (modelNumeral M 19+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 7+rc)
  let cs := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
  change F PA194Stepper.stepper ![F addCode ![c0,modelNumeral M 18+cs],_] = _
  rw [PA194StepperCompose.modelStepperCompose,first,second]
#print axioms twoPassesTo71
end models
end PA194Site29TwoPassesTo71
