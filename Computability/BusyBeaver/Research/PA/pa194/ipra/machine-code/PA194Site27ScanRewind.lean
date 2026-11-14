import PA194HalfFileSixWithTail
import PA194SixRewind
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site27ScanRewind
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194HalfFileSixWithTail PA194SixRewind PA194RegisterFile PA194UnaryRuns PA194FileTraversal
open PA194BinaryDouble BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem scanAndRewind (e : Fin 11 → M) (b p : M)
    (hp : F (fileCode 10) e = p+p) :
    let base := (b+b+1)+(b+b+1)
    let e0 := e
    let e1 : Fin (3+7) → M := fun j => e0 j.succ
    let e2 : Fin (3+6) → M := fun j => e1 j.succ
    let e3 : Fin (3+5) → M := fun j => e2 j.succ
    let e4 : Fin (3+4) → M := fun j => e3 j.succ
    let e5 : Fin (3+3) → M := fun j => e4 j.succ
    let e6 : Fin (3+2) → M := fun j => e5 j.succ
    let x1 := F ones ![e0 0+1,base]
    let l1 := x1+x1
    let t1 := (e0 0+1)+1
    let x2 := F ones ![e1 0+1,l1]
    let l2 := x2+x2
    let t2 := (e1 0+1)+1
    let x3 := F ones ![e2 0+1,l2]
    let l3 := x3+x3
    let t3 := (e2 0+1)+1
    let x4 := F ones ![e3 0+1,l3]
    let l4 := x4+x4
    let t4 := (e3 0+1)+1
    let x5 := F ones ![e4 0+1,l4]
    let l5 := x5+x5
    let t5 := (e4 0+1)+1
    let x6 := F ones ![e5 0+1,l5]
    let l6 := x6+x6
    let t6 := (e5 0+1)+1
    let r6 := F ones ![e6 0+1,F (fileCode 3) (fun i => e6 i.succ)]
    let six : Fin 7 → M := ![e 0,e 1,e 2,e 3,e 4,e 5,(0 : M)]
    let tail := F (fileCode 3) (fun i => e6 i.succ)
    let q := F ones ![e6 0,tail]
    let out := F (fileCode 6) ![e 0,e 1,e 2,e 3,e 4,e 5,(q+q)+(q+q)]
    let rev : Fin 6 → M := ![e 4,e 3,e 2,e 1,e 0,base]
    let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
    let cr := (modelNumeral M 2+((e 5+1)+1))+F (PA194CarryFile.costCode 5) rev
    F PA194Stepper.stepper ![c6+cr,F pairCode ![modelNumeral M 71,F pairCode ![base,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+out+out]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let base := (b+b+1)+(b+b+1)
  let e0 := e
  let e1 : Fin 10 → M := fun j => e0 j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let l0 := base
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
  let six : Fin 7 → M := ![e 0,e 1,e 2,e 3,e 4,e 5,(0 : M)]
  let tail := F (fileCode 3) (fun i => e6 i.succ)
  let q := F ones ![e6 0,tail]
  let rev : Fin 6 → M := ![e 4,e 3,e 2,e 1,e 0,base]
  let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
  let cr := (modelNumeral M 2+((e 5+1)+1))+F (PA194CarryFile.costCode 5) rev
  have hscan := scanSixExact 3 e base p hp
  dsimp only at hscan
  have hr : F ones ![e6 0+1,tail] = q+q+1 := by
    change F ones ![F addCode ![e6 0,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hr] at hscan
  have hl : F (leftCode 6) (Fin.cases base six) = l6 := by
    dsimp only [l6,xx6,l5,xx5,l4,xx4,l3,xx3,l2,xx2,l1,xx1,six,e0,e1,e2,e3,e4,e5]
    simp only [modelLeftSucc,modelLeftZero,modelBlock]
    rfl
  have hrew := sixTo17 six b q
  dsimp only at hrew
  rw [hl] at hrew
  let out := F (fileCode 6) ![e 0,e 1,e 2,e 3,e 4,e 5,(q+q)+(q+q)]
  change F PA194Stepper.stepper ![cr,F pairCode ![modelNumeral M 14,F pairCode ![l6,q+q+1]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+out+out]] at hrew
  change F PA194Stepper.stepper ![F addCode ![c6,cr],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hscan.2,hrew]
#print axioms scanAndRewind
end models
end PA194Site27ScanRewind
