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
import PA194Site27ScanRewind
import PA194Site27To17
import PA194Site27Unmark
import PA194Site27SecondRoot
import PA194Site27RootTo1
import PA194Site27To1
import PA194Site27CarryTo4
import PA194Site27To4
import PA194Site27BranchRows
import PA194Site27PositiveTo6
import PA194Site27PositiveSix
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27PositiveReturned
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

theorem site27PositiveReturned (k m : M) (e : Fin 11 → M) (hm : e 0 = m+1) :
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
    let b := F ones ![k+1,aa6+aa6]
    let base := (b+b+1)+(b+b+1)
    let e0 := v
    let e1 : Fin 10 → M := fun j => e0 j.succ
    let e2 : Fin 9 → M := fun j => e1 j.succ
    let e3 : Fin 8 → M := fun j => e2 j.succ
    let e4 : Fin 7 → M := fun j => e3 j.succ
    let e5 : Fin 6 → M := fun j => e4 j.succ
    let e6 : Fin 5 → M := fun j => e5 j.succ
    let t1 := (e0 0+1)+1
    let t2 := (e1 0+1)+1
    let t3 := (e2 0+1)+1
    let t4 := (e3 0+1)+1
    let t5 := (e4 0+1)+1
    let t6 := (e5 0+1)+1
    let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
    let q := F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)]
    let out := F (fileCode 6) ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
    let rev : Fin 6 → M := ![v 4,v 3,v 2,v 1,v 0,base]
    let cr := (modelNumeral M 2+((v 5+1)+1))+F (PA194CarryFile.costCode 5) rev
    let qf := out+out+1
    let w := F ones ![k+1,qf]
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let z := (1 : M)+w3+w3
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let croot := (((((1 : M)+k)+1)+1)+(modelNumeral M 3+(modelNumeral M 3+rc)))
    let vec : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
    let before := F ones ![k+1,(aa6+aa6)+(aa6+aa6)]
    let carried := F (PA194CarryFile.leftCode 6) (Fin.cases before vec)
    let selectedLeft := carried+carried+1
    let ccarry := ((k+1)+F (PA194CarryFile.costCode 6) vec)+modelNumeral M 2
    let tail := F (fileCode 3) (fun i => e6 i.succ)
    let rp := F ones ![m,tail]
    let file0 := rp+rp+1
    let f1 := F ones ![v 5,(file0+file0)+(file0+file0)+1]
    let ct1 := (1 : M)+(v 5+1)
    let f2 := F ones ![v 4,(f1+f1)+(f1+f1)+1]
    let ct2 := (1 : M)+(v 4+1)
    let f3 := F ones ![v 3,(f2+f2)+(f2+f2)+1]
    let ct3 := (1 : M)+(v 3+1)
    let f4 := F ones ![v 2,(f3+f3)+(f3+f3)+1]
    let ct4 := (1 : M)+(v 2+1)
    let f5 := F ones ![v 1,(f4+f4)+(f4+f4)+1]
    let ct5 := (1 : M)+(v 1+1)
    let f6 := F ones ![v 0,(f5+f5)+(f5+f5)+1]
    let ct6 := (1 : M)+(v 0+1)
    let cret := (((((ct1+ct2)+ct3)+ct4)+ct5)+ct6)
    let clock := (((((((((modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 5+rc))+modelNumeral M 8)+(n+1))+(c6+cr))+croot)+modelNumeral M 13)+ccarry)+modelNumeral M 1)+cret
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),u6+u6+1]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![before+before+1,f6+f6]] := by
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
  let b := F ones ![k+1,aa6+aa6]
  let base := (b+b+1)+(b+b+1)
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
  let rev : Fin 6 → M := ![v 4,v 3,v 2,v 1,v 0,base]
  let cr := (modelNumeral M 2+((v 5+1)+1))+F (PA194CarryFile.costCode 5) rev
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let q := F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)]
  let out := F (fileCode 6) ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
  let croot := (((((1 : M)+k)+1)+1)+(modelNumeral M 3+(modelNumeral M 3+rc)))
  let qf := out+out+1
  let vec : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
  let ccarry := ((k+1)+F (PA194CarryFile.costCode 6) vec)+modelNumeral M 2
  let before := F ones ![k+1,(aa6+aa6)+(aa6+aa6)]
  let carried := F (PA194CarryFile.leftCode 6) (Fin.cases before vec)
  let selectedLeft := carried+carried+1
  let tail := F (fileCode 3) (fun i => e6 i.succ)
  let rp := F ones ![m,tail]
  let file0 := rp+rp+1
  let ct1 := (1 : M)+(v 5+1)
  let ct2 := (1 : M)+(v 4+1)
  let ct3 := (1 : M)+(v 3+1)
  let ct4 := (1 : M)+(v 2+1)
  let ct5 := (1 : M)+(v 1+1)
  let ct6 := (1 : M)+(v 0+1)
  let cret := (((((ct1+ct2)+ct3)+ct4)+ct5)+ct6)
  have h6 := PA194Site27PositiveTo6.site27PositiveTo6 k m e hm
  dsimp only at h6
  have hret := PA194Site27PositiveSix.returnSix vec before file0
  dsimp only at hret
  let f1 := F ones ![v 5,(file0+file0)+(file0+file0)+1]
  let f2 := F ones ![v 4,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![v 3,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![v 2,(f3+f3)+(f3+f3)+1]
  let f5 := F ones ![v 1,(f4+f4)+(f4+f4)+1]
  let f6 := F ones ![v 0,(f5+f5)+(f5+f5)+1]
  change F PA194Stepper.stepper ![cret,F pairCode ![modelNumeral M 6,
      F pairCode ![selectedLeft,file0+file0]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![before+before+1,f6+f6]] at hret
  change F PA194Stepper.stepper ![F addCode ![(((((c+(modelNumeral M 5+rc))+modelNumeral M 8)+(n+1))+(c6+cr))+croot)+modelNumeral M 13+ccarry+modelNumeral M 1,cret],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h6,hret]
#print axioms site27PositiveReturned
end models
end PA194Site27PositiveReturned
