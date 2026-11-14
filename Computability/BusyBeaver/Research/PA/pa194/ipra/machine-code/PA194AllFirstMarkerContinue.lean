import PA194MarkerZeroIncrementContinue
import PA194MarkerIncrementContinueTwo
import PA194IncrementContinueTwo
import PA194MarkerToIncrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194AllFirstMarkerContinue
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveMarkCycle PA194ReturnedDecrement PA194ReturnFileMeaning
open PA194MarkedCycleDecrement PA194DecrementFirstReturn PA194MarkerPositiveReturn
open PA194SevenToSixteen PA194ReturnedUpdatedEven PA194MarkerPositiveSixteen PA194SixteenHeaderReturn
open PA194MarkerHeaderRecurrence PA194HeaderTo84 PA194IncrementDispatch PA194HeaderController
open PA194UpdatedSevenOdd PA194UpdatedSevenBlank PA194SevenRewind
open PA194MarkerMarkedBlank PA194MarkedExitIncrement
open PA194MarkerTo84 PA194EightyFourTo17 PA194MarkerSecond17 PA194Second17Return
open PA194MarkerZeroIncrementContinue PA194MarkerIncrementContinueTwo PRAExhaustion PA194MarkerToIncrement PA194IncrementContinueTwo
open PA194MarkerThird17 PA194OddHeaderTo106 PA194MarkerTo106 PA194UpdatedSevenMatch
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan PA194MarkedFile
open PRAModelIOpenPairing TableDispatch
open PA194UpdatedSevenOdd PA194UpdatedSevenBlank PA194SevenRewind
open PA194MarkerMarkedBlank PA194MarkedExitIncrement
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- Both possible first-block cases reach dense 24 with the same controller
half. This is conditional on the stated intermediate marker configuration. -/
theorem allFirstMarkerToContinue (idx n : Nat) (bound : idx+1 < 9)
    (hn : idx+n=7)
    (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (v u k : M)
    (ht : e (Fin.last (idx+1)) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hblank : rest (Fin.last (n+1)) = (0 : M))
    (hfirst : e 0 = ((((((k+1)+1)+1)+1)+1)+1)+1)
    (hv : v ≠ (0 : M)) :
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
  dsimp only
  have hex := modelZeroOrSuccPred k
  change k = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => k)) = k at hex
  rcases hex with hk | hk
  · have hm := markerZeroToContinueTarget idx n bound hn e rest v u k ht hblank hfirst hv hk
    dsimp only at hm
    simp only [hv,if_false] at hm
    obtain ⟨r,file,t,s,next,spare,hr,hfile,htail,hs,hones,hinc,rr,hrr,time,htime⟩ := hm
    exact ⟨time,_,htime⟩
  · let j := F predCode (fun _ => k)
    have hj : k = j+1 := by
      have ha : F Code.succ (fun _ => j) = j+1 := (modelAddOne j).symm
      exact hk.symm.trans ha
    have hm := markerToContinueTarget idx n bound hn e rest v u k j ht hblank hfirst hv hj
    dsimp only at hm
    simp only [hv,if_false] at hm
    obtain ⟨r,file,t,s,next,spare,hr,hfile,htail,hs,hones,hinc,rr,hrr,time,htime⟩ := hm
    exact ⟨time,_,htime⟩
#print axioms allFirstMarkerToContinue
end models
end PA194AllFirstMarkerContinue
