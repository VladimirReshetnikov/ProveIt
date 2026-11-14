import PA194MarkerFirstSixPositiveTo24
import PA194MarkerZeroSelectedTo24
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstSixAllTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkerFirstSixPositiveTo24 PA194MarkerZeroSelectedTo24
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveThreshold PA194HeaderController PA194PositiveMarkerRoute PA194ThresholdCycle
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan
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

/-- All eight non-first marker positions reach state 15 for a first
physical value five, using the actual following register file. -/
theorem markerFirstSixAllTo24 (idx n : Nat) (bound : idx+1 < 9)
    (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (u v : M)
    (ht : e (Fin.last (idx+1)) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = (((((0 : M)+1)+1)+1)+1)+1+1) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    ∃ time right : M,
      F PA194Stepper.stepper ![time,
        F pairCode ![modelNumeral M (markerControl ⟨idx+1,bound⟩),F pairCode ![x+x+1,F (fileCode (idx+1)) e]]] =
      F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  classical
  by_cases hv : v = (0 : M)
  · have hm := markerZeroTo24 idx n bound e rest v u (0 : M) ht hfirst hv
    dsimp only at hm ⊢
    simp only [hv,ite_true] at hm
    obtain ⟨rr,hr,hm⟩ := hm
    exact ⟨_,_,hm⟩
  · have hm := markerFirstSixPositiveTo24 idx n bound e rest v u ht hfirst hv
    dsimp only at hm ⊢
    simp only [hv,if_false] at hm
    obtain ⟨rr,hr,hm⟩ := hm
    exact ⟨_,_,hm⟩
#print axioms markerFirstSixAllTo24
end models
end PA194FirstSixAllTo24
