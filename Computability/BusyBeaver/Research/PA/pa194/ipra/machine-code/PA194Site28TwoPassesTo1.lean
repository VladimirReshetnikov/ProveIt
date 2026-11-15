import PA194Site28ScanTo1
import PA194Site28TwoPassesTo2
import PA194Site28TwoPasses
import PA194Site28ThirdDispatch
import PA194Site28SecondPass
import PA194SecondHeaderFile
import PA194Site28HeaderPass
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28TwoPassesTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28ScanTo1 PA194Site28TwoPassesTo2 PA194Site28TwoPasses PA194Site28ThirdDispatch PA194Site28HeaderPass PA194Site28SecondPass PA194SecondHeaderFile PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194OnesCommute PA194ZeroRuns
open PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem twoPassesTo1 (k : M) (args : Fin 11 → M) :
    let v := physicalArgs args
    let f := F sourceFileCode args
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let r := F ones ![k,t]
    let e : Fin 12 → M := Fin.cases (k+1) v
    let e1 : Fin 11 → M := fun i => e i.succ
    let e2 : Fin 10 → M := fun i => e1 i.succ
    let b := F ones ![e2 0,F (fileCode 8) (fun i => e2 i.succ)]
    let c := (b+b)+(b+b)
    let w1 := F ones ![e1 0,(1 : M)+c+c]
    let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
    let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
    let backClock := (e1 0+1)+((e 0+1)+1)
    let s0 := r+r+1
    let z0 := s0+s0
    let z1 := z0+z0+1
    let z2 := z1+z1
    let z3 := z2+z2+1
    let z4 := z3+z3
    let z5 := z4+z4
    let z6 := z5+z5
    let v1 := w2+w2
    let v2 := v1+v1
    let v3 := v2+v2
    let x0 := v3+1
    let x1 := x0+x0
    let x2 := x1+x1+1
    let x3 := x2+x2
    let x4 := x3+x3
    let x5 := x4+x4
    let x6 := x5+x5+1
    let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let s := F zeros ![k,f+f+1]
    let t0 := s+s
    let t1 := t0+t0
    let u0 := t1+t1
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let c0 := modelNumeral M 16+(((((k+1)+1)+1)+1)+((k+1)+1))
    let c1 := (modelNumeral M 4+modelNumeral M 2)+returnClock
    let c2 := ((modelNumeral M 9+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 7)+returnClock
    let r2 := F ones ![k,(1 : M)+(w1+w1)+(w1+w1)]
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6
    let l0 := (a7+a7)+(a7+a7)
    let d0 := F ones ![k,l0]
    let d1 := d0+d0+1
    let d2 := d1+d1
    let d3 := d2+d2+1
    let d4 := F ones ![v 0,d3]
    let scan := ((k+modelNumeral M 2)+(modelNumeral M 1+v 0))+modelNumeral M 2
    F PA194Stepper.stepper ![(((c0+c1)+c2)+modelNumeral M 16)+scan,
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),u6+u6+1]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(d4+d4)+(d4+d4)+1,b]] := by
  dsimp only
  let v := physicalArgs args
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let r := F ones ![k,t]
  let e : Fin 12 → M := Fin.cases (k+1) v
  let e1 : Fin 11 → M := fun i => e i.succ
  let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
  let backClock := (e1 0+1)+((e 0+1)+1)
  let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c0 := modelNumeral M 16+(((((k+1)+1)+1)+1)+((k+1)+1))
  let c1 := (modelNumeral M 4+modelNumeral M 2)+returnClock
  let c2 := ((modelNumeral M 9+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 7)+returnClock
  let e2 : Fin 10 → M := fun i => e1 i.succ
  let b := F ones ![e2 0,F (fileCode 8) (fun i => e2 i.succ)]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e1 0,(1 : M)+c+c]
  let r2 := F ones ![k,(1 : M)+(w1+w1)+(w1+w1)]
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5+1
  let a7 := a6+a6
  let l0 := (a7+a7)+(a7+a7)
  let c3 := ((k+modelNumeral M 2)+(modelNumeral M 1+v 0))+modelNumeral M 2
  have h2 := PA194Site28TwoPassesTo2.twoPassesTo2 k args
  dsimp only at h2
  have h1 := PA194Site28ScanTo1.scanTo1 (M := M) k (v 0) l0 b
  dsimp only at h1
  change F PA194Stepper.stepper ![F addCode ![((c0+c1)+c2)+modelNumeral M 16,c3],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h2]
  change F PA194Stepper.stepper ![c3,F pairCode ![modelNumeral M 2,F pairCode ![l0,r2]]] = _
  exact h1
#print axioms twoPassesTo1
end models
end PA194Site28TwoPassesTo1
