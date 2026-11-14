import PA194PositiveMarkCycle
import PA194ReturnedDecrement
import PA194DecrementFirstReturn
import PA194MarkedCycleDecrement
import PA194SevenReturnController
import PA194MarkerPositiveReturn
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194MarkerPositiveScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveMarkCycle PA194ReturnedDecrement PA194ReturnFileMeaning
open PA194MarkedCycleDecrement PA194DecrementFirstReturn PA194MarkerPositiveReturn PA194SevenReturnController
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan PA194MarkedFile
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem markerPositiveScan (idx n : Nat) (bound : idx+1 < 9)
    (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (v u m : M)
    (ht : e (Fin.last (idx+1)) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = (((((m+1)+1)+1)+1)+1)+1)
    (hv : v ≠ (0 : M)) :
    letI : DecidableEq M := Classical.decEq M
    let tail := F (fileCode (n+1)) rest
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let ep := replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F markedBlock ![v,tail])
    let cost := F (costCode idx) ep
    let pred := F predCode (fun _ => v)
    let p := F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F block ![pred,tail]))
    let isZero := v = (0 : M)
    let markClock := (F (costCode (idx+1)) e+modelNumeral M 3)+F (costCode (idx+1)) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c1 := modelNumeral M 6+((modelNumeral M 3+1)+1)
    let cycleClock := (((c1+headerClock)+modelNumeral M 3)+modelNumeral M 3)+1
    let phaseClock := ((markClock+headerClock)+modelNumeral M 3)+cycleClock
    let decrementClock := (modelNumeral M 2+m)+((cost+(if isZero then modelNumeral M 7 else modelNumeral M 4))+cost)
    let scanLeft := ((a3+1)+(a3+1))
    F PA194Stepper.stepper ![((phaseClock+decrementClock)+((m+1)+1))+
        (modelNumeral M 3+(((1 : M)+1)+m)),
      F pairCode ![modelNumeral M (markerControl ⟨idx+1,bound⟩),F pairCode ![x+x+1,F (fileCode (idx+1)) e]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![F zeros ![m,(scanLeft+scanLeft)+(scanLeft+scanLeft)],p]] := by
  classical
  dsimp only
  have hm := markerPositiveReturn idx n bound e rest v u m ht hfirst hv
  dsimp only at hm
  simp only [hv,if_false] at hm ⊢
  apply continueThroughFirst
  exact hm
#print axioms markerPositiveScan
end models
end PA194MarkerPositiveScan
