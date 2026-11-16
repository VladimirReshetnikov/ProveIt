import PA194RegisterPermutation
import PA194HalfFileSixWithTail
import PA194ScanSixRewindWithTail
import PA194SixRewind
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site29ScanRewind
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation TableDispatch PA194HalfFileSixWithTail PA194SixRewind PA194RegisterFile PA194UnaryRuns PA194FileTraversal
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

theorem scanAndRewind (args : Fin 11 → M) (b : M) :
    let e : Fin 9 → M := fun i => physicalArgs args i.succ.succ
    let p := F ones ![e 0+1,F (fileCode 7) (fun i => e i.succ)]
    let base := (b+b+1)+(b+b+1)
    let e0 := e
    let e1 : Fin (1+7) → M := fun j => e0 j.succ
    let e2 : Fin (1+6) → M := fun j => e1 j.succ
    let e3 : Fin (1+5) → M := fun j => e2 j.succ
    let e4 : Fin (1+4) → M := fun j => e3 j.succ
    let e5 : Fin (1+3) → M := fun j => e4 j.succ
    let e6 : Fin (1+2) → M := fun j => e5 j.succ
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
    let r6 := F ones ![e6 0+1,F (fileCode 1) (fun i => e6 i.succ)]
    let six : Fin 7 → M := ![e 0,e 1,e 2,e 3,e 4,e 5,(0 : M)]
    let tail := F (fileCode 1) (fun i => e6 i.succ)
    let q := F ones ![e6 0,tail]
    let out := F (fileCode 6) ![e 0,e 1,e 2,e 3,e 4,e 5,(q+q)+(q+q)]
    let rev : Fin 6 → M := ![e 4,e 3,e 2,e 1,e 0,base]
    let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
    let cr := (modelNumeral M 2+((e 5+1)+1))+F (PA194CarryFile.costCode 5) rev
    F PA194Stepper.stepper ![c6+cr,F pairCode ![modelNumeral M 71,F pairCode ![base,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+out+out]] := by
  dsimp only
  let e : Fin 9 → M := fun i => physicalArgs args i.succ.succ
  let p := F ones ![e 0+1,F (fileCode 7) (fun i => e i.succ)]
  have hp : F (fileCode 8) e = p+p := by rw [modelFileSucc,modelBlock]
  exact PA194ScanSixRewindWithTail.scanAndRewind 1 e b p hp
#print axioms scanAndRewind
end models
end PA194Site29ScanRewind
