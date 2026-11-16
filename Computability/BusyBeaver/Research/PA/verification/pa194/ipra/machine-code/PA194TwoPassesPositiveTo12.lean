import PA194SecondHeaderFile
import PA194ThirdHeaderTo1
import PA194TwoHeaderPasses
import PA194TwoPassesTo1
import PA194TwoPassesScan
import PA194TwoPassesTo4
import PA194RightRows
import PA194LeftOneWriteOne
import PA194TwoPassesPositiveTo6
import PA194IncrementTail
import PA194TwoPassesPositiveTo7
import PA194PositiveRewind
import PA194TwoPassesPositiveRewind
import PA194PositiveHeaderTo12
import PA194ThirdPassTo4
import PA194OnesCommute
import PA194ScanInvariant
import PA194SeedHeaderPass
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194TwoPassesPositiveTo12
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderPass PA194SecondHeaderPass PA194SecondHeaderFile PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194OnesCommute PA194ZeroRuns
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

theorem twoPassesPositiveTo12 (k m : M) (args : Fin 11 → M) (hm : args 8 = m+1) :
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
    let z0 := r+r+1
    let z1 := z0+z0
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let z5 := z4+z4
    let v1 := w2+w2
    let v2 := v1+v1
    let v3 := v2+v2
    let v4 := v3+v3
    let v5 := v4+v4
    let v6 := v5+v5
    let v7 := v6+v6
    let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let s := F zeros ![k,f+f+1]
    let y0 := s+s
    let y1 := y0+y0
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let y5 := y4+y4
    let y6 := y5+y5
    let c0 := (modelNumeral M 12 + (((((k+1)+1)+1)+1)+((k+1)+1))) + modelNumeral M 4
    let c1 := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c2 := ((modelNumeral M 7+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 5)+returnClock
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3
    let a5 := a4+a4
    let initial := (a5+a5)+(a5+a5)
    let scanLeft := F ones ![k,initial]
    let l1 := scanLeft+scanLeft+1
    let l2 := l1+l1+1
    let a := F ones ![e1 0,l2+l2]
    let z := (a+a+1)+(a+a+1)
    let rem : Fin 9 → M := fun i => e2 i.succ
    let rp := F ones ![m,F (fileCode 8) rem]
    let tp := rp+rp+1
    let rf := tp+tp
    let file := rf+rf+1
    let final := F ones ![e1 0,file]
    let q := (final+final)+(final+final)+1
    let w := F ones ![k+1,q]
    F PA194Stepper.stepper ![((((((((c0+c1)+c2)+modelNumeral M 12)+k)+((modelNumeral M 3+e1 0)+modelNumeral M 2))+modelNumeral M 1)+modelNumeral M 1 )+(e1 0+1))+((modelNumeral M 2+k)+modelNumeral M 4),
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),y6+y6+1]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![a4+a4+1,(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
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
  let c0 := (modelNumeral M 12 + (((((k+1)+1)+1)+1)+((k+1)+1))) + modelNumeral M 4
  let c1 := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c2 := ((modelNumeral M 7+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 5)+returnClock
  let e2 : Fin 10 → M := fun i => e1 i.succ
  let b := F ones ![e2 0,F (fileCode 8) (fun i => e2 i.succ)]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e1 0,(1 : M)+c+c]
  let x := F ones ![k,(1 : M)+(w1+w1)+(w1+w1)]
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3
  let a5 := a4+a4
  let initial := (a5+a5)+(a5+a5)
  let scanLeft := F ones ![k,initial]
  let l1 := scanLeft+scanLeft+1
  let l2 := l1+l1+1
  let a := F ones ![e1 0,l2+l2]
  let z := (a+a+1)+(a+a+1)
  let rem : Fin 9 → M := fun i => e2 i.succ
  let rp := F ones ![m,F (fileCode 8) rem]
  let tp := rp+rp+1
  let rf := tp+tp
  let file := rf+rf+1
  let final := F ones ![e1 0,file]
  have h := PA194TwoPassesPositiveRewind.twoPassesPositiveRewind k m args hm
  dsimp only at h
  have h12 := PA194PositiveHeaderTo12.positiveHeaderTo12 k a4 final
  dsimp only at h12
  change F PA194Stepper.stepper ![F addCode ![((((((c0+c1)+c2)+modelNumeral M 12)+k)+((modelNumeral M 3+e1 0)+modelNumeral M 2)+modelNumeral M 1)+modelNumeral M 1)+(e1 0+1),(modelNumeral M 2+k)+modelNumeral M 4],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h,h12]
#print axioms twoPassesPositiveTo12
end models
end PA194TwoPassesPositiveTo12
