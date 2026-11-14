import PA194Site27HeaderDispatch
import PA194EightyFourTo17
import PA194RegisterPermutation
import PA194HeaderController
import PA194Site27HeaderTo17
import PA194Site27HeaderReturn
import PA194Site27HeaderPass
import PA194Site27SecondDispatch
import PA194Site27To106
import PA194Site27Scan106
import PA194Site27To71
import PA194HalfFileSixWithTail
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27To14
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site27HeaderDispatch PA194EightyFourTo17 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194HeaderController BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem site27To14 (k : M) (e : Fin 11 → M) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let r := F zeros ![k,f+f+1]
    let s := r+r
    let u0 := s+s
    let u1 := u0+u0
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
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let w := F ones ![k+1,t]
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let x := w3+1
    let x1 := x+x
    let x2 := x1+x1
    let x3 := x2+x2
    let x4 := x3+x3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let rhalf := F ones ![k,t]
    let aa0 := (1 : M)+(1 : M)+1
    let aa1 := aa0+aa0
    let aa2 := aa1+aa1
    let aa3 := aa2+aa2
    let aa4 := aa3+aa3+1
    let aa5 := aa4+aa4
    let aa6 := aa5+aa5
    let n := (k+1)+1
    let a := F ones ![n,aa6+aa6]
    let e0 := v
    let e1 : Fin 10 → M := fun j => e0 j.succ
    let e2 : Fin 9 → M := fun j => e1 j.succ
    let e3 : Fin 8 → M := fun j => e2 j.succ
    let e4 : Fin 7 → M := fun j => e3 j.succ
    let e5 : Fin 6 → M := fun j => e4 j.succ
    let e6 : Fin 5 → M := fun j => e5 j.succ
    let l0 := a+a
    let xx1 := F ones ![e0 0+1,l0]
    let l1 := xx1+xx1
    let t1 := (e0 0+1)+1
    let xx2 := F ones ![e1 0+1,l1]
    let l2 := xx2+xx2
    let t2 := (e1 0+1)+1
    let xx3 := F ones ![e2 0+1,l2]
    let l3 := xx3+xx3
    let t3 := (e2 0+1)+1
    let xx4 := F ones ![e3 0+1,l3]
    let l4 := xx4+xx4
    let t4 := (e3 0+1)+1
    let xx5 := F ones ![e4 0+1,l4]
    let l5 := xx5+xx5
    let t5 := (e4 0+1)+1
    let xx6 := F ones ![e5 0+1,l5]
    let l6 := xx6+xx6
    let t6 := (e5 0+1)+1
    let r6 := F ones ![e6 0+1,F (fileCode 3) (fun i => e6 i.succ)]
    let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
    let clock := ((((modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 5+rc))+modelNumeral M 8)+(n+1))+c6
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),u6+u6+1]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![l6,r6]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let w := F ones ![k+1,t]
  let c := modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1))
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let rhalf := F ones ![k,t]
  let aa0 := (1 : M)+(1 : M)+1
  let aa1 := aa0+aa0
  let aa2 := aa1+aa1
  let aa3 := aa2+aa2
  let aa4 := aa3+aa3+1
  let aa5 := aa4+aa4
  let aa6 := aa5+aa5
  let n := (k+1)+1
  let a := F ones ![n,aa6+aa6]
  let e0 := v
  let e1 : Fin 10 → M := fun j => e0 j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let t1 := (e0 0+1)+1
  let t2 := (e1 0+1)+1
  let t3 := (e2 0+1)+1
  let t4 := (e3 0+1)+1
  let t5 := (e4 0+1)+1
  let t6 := (e5 0+1)+1
  let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
  have hf : F (fileCode 10) v = p+p := by rw [modelFileSucc,modelBlock]
  have h71 := PA194Site27To71.site27To71 k e
  dsimp only at h71
  have h14 := PA194HalfFileSixWithTail.scanSixExact 3 v (a+a) p hf
  dsimp only at h14
  change F PA194Stepper.stepper ![F addCode ![((c+(modelNumeral M 5+rc))+modelNumeral M 8)+(n+1),c6],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h71,h14.2]
#print axioms site27To14
end models
end PA194Site27To14
