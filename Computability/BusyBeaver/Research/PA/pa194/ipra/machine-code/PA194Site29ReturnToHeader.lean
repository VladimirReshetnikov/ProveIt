import PA194Site29ReturnThree
import PA194Site29To17
import PA194Site29ScanRewind
import PA194Site29TwoPassesTo71
import PA194Site29HeaderPass
import PA194Site29SecondPassTo71
import PA194Site29SecondDispatch
import PA194Site29ScanTo71
import PA194SecondHeaderFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnToHeader
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
theorem site29ReturnToHeader (k : M) (args : Fin 11 → M) :
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
    let b0 := F ones ![v 1,l5]
    let e : Fin 9 → M := fun i => v i.succ.succ
    let e6 : Fin 3 → M := fun i => e i.succ.succ.succ.succ.succ.succ
    let f6 := F (fileCode 1) (fun i => e6 i.succ)
    let q := F ones ![e6 0,f6]
    let out := F (fileCode 6) ![e 0,e 1,e 2,e 3,e 4,e 5,(q+q)+(q+q)]
    let base := (b0+b0+1)+(b0+b0+1)
    let rev : Fin 6 → M := ![e 4,e 3,e 2,e 1,e 0,base]
    let t1 := (e 0+1)+1
    let t2 := (e 1+1)+1
    let t3 := (e 2+1)+1
    let t4 := (e 3+1)+1
    let t5 := (e 4+1)+1
    let t6 := (e 5+1)+1
    let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
    let cr := (modelNumeral M 2+((e 5+1)+1))+F (PA194CarryFile.costCode 5) rev
    let aR1 := F ones ![v 1,(1 : M)+out+out]
    let aR2 := F ones ![v 0,(1 : M)+(aR1+aR1)+(aR1+aR1)]
    let aR3 := F ones ![k+1,(1 : M)+(aR2+aR2)+(aR2+aR2)]
    let ct := (((v 1+1)+1)+((v 0+1)+1))+(((k+1)+1)+1)
    F PA194Stepper.stepper ![((firstClock+(modelNumeral M 18+cscan))+(c6+cr))+ct,
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),z9+z9+1]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![cc,(aR3+aR3)+(aR3+aR3)]] := by
  dsimp only
  let v := physicalArgs args
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
  let l0 := F ones ![k,l]
  let l1 := l0+l0+1
  let l2 := l1+l1+1
  let l3 := l2+l2
  let l4 := F ones ![v 0+1,l3]
  let l5 := l4+l4
  let b0 := F ones ![v 1,l5]
  let e : Fin 9 → M := fun i => v i.succ.succ
  let e6 : Fin 3 → M := fun i => e i.succ.succ.succ.succ.succ.succ
  let f6 := F (fileCode 1) (fun i => e6 i.succ)
  let q := F ones ![e6 0,f6]
  let out := F (fileCode 6) ![e 0,e 1,e 2,e 3,e 4,e 5,(q+q)+(q+q)]
  let base := (b0+b0+1)+(b0+b0+1)
  let rev : Fin 6 → M := ![e 4,e 3,e 2,e 1,e 0,base]
  let c6 := ((((((e 0+1)+1)+((e 1+1)+1))+((e 2+1)+1))+((e 3+1)+1))+((e 4+1)+1))+((e 5+1)+1)
  let cr := (modelNumeral M 2+((e 5+1)+1))+F (PA194CarryFile.costCode 5) rev
  let ct := (((v 1+1)+1)+((v 0+1)+1))+(((k+1)+1)+1)
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c0 := (modelNumeral M 19+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 7+rc)
  let cs := ((k+modelNumeral M 3)+((v 0+1)+1))+((v 1+1)+1)
  have first := PA194Site29To17.site29To17 k args
  dsimp only at first
  change F PA194Stepper.stepper ![_,_] = F pairCode ![modelNumeral M 17,F pairCode ![b0,(1 : M)+out+out]] at first
  have second := PA194Site29ReturnThree.returnThree k (v 0) (v 1) cc out
  dsimp only at second
  change F PA194Stepper.stepper ![F addCode ![(c0+(modelNumeral M 18+cs))+(c6+cr),ct],_] = _
  rw [PA194StepperCompose.modelStepperCompose,first]
  exact second
#print axioms site29ReturnToHeader
end models
end PA194Site29ReturnToHeader
