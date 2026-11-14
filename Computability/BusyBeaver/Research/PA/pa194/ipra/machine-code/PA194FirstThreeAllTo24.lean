import PA194FirstThreeZeroTo24
import PA194FirstThreeBlankTailTo24
import PA194FirstFiveFifteenTo24
import PA194FirstThreeFirstTo42
import PA194State42Boundary
import PA194EightyFourScan
import PA194HeaderController
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstThreeAllTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFiveFifteenTo24 PA194State42Boundary PA194EightyFourScan PA194HeaderController PA194FiniteControls PA194StateOne PA194FirstThreeFirstTo42 PA194FirstThreeBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveThreshold PA194HeaderController PA194PositiveMarkerRoute PA194ThresholdCycle
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan
open PRAModelIOpenPairing TableDispatch PRAExhaustion
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The first-three first non-first marker reaches dense 24 for any selected value under the common blank-tail layout. -/
theorem markerFirstThreeAllTo24 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u v : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 3)
    (hblank : rest (Fin.last (n+1)) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    ∃ time right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hex := modelZeroOrSuccPred v
  change v = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => v)) = v at hex
  rcases hex with hv | hv
  · subst v
    exact PA194FirstThreeZeroTo24.markerFirstThreeZeroTo24 n e rest u ht hfirst
  · let k := F predCode (fun _ => v)
    have hk : v=k+1 := by
      have ha : F Code.succ (fun _ => k) = k+1 := (modelAddOne k).symm
      exact hv.symm.trans ha
    rw [hk] at ht
    obtain ⟨t,hh⟩ := PA194FirstThreeBlankTailTo24.markerFirstThreeBlankTailTo24 n e rest u k ht hfirst hblank
    exact ⟨t,_,hh⟩
#print axioms markerFirstThreeAllTo24
end models
end PA194FirstThreeAllTo24
