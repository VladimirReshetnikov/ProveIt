import PA194CarryThreeOddFile
import PA194FirstThreePositiveScan
import PA194ScanInvariant
import PA194CarryEntry
import PA194FirstThreeFirstTo42
import PA194State42Boundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CarryThreeExactFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ScanInvariant PA194CarryEntry PA194StateOne PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

/-- The folded left tape after consuming each block. The recursion is on the
fixed external file length, while all values are interpreted in the model. -/
def carried : (n : Nat) → (Fin (n+1) → M) → M → M → M
  | 0, _, v, l => F ones ![v,l+l]
  | n+1, e, v, l =>
      carried n (fun i => e i.succ) (e 0)
        (F ones ![v,l+l]+F ones ![v,l+l]+1)

theorem carryThreeAcrossExact (n : Nat) (e : Fin (n+1) → M) (v l p : M)
    (hend : e (Fin.last n) = p+p) :
    ∃ time : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![v+1,F (fileCode n) e]]]] =
      F pairCode ![modelNumeral M 3,F pairCode ![carried n e v l+carried n e v l+1,p]] := by
  induction n generalizing v l with
  | zero =>
    have he : F (fileCode 0) e = p+p := by
      change F (.proj 0) e = _
      rw [modelProjection]
      exact hend
    refine ⟨(1 : M)+(v+1), ?_⟩
    rw [he]
    exact PA194CarryThreeOddFile.cycleThree v l p
  | succ n ih =>
    let ee : Fin (n+1) → M := fun i => e i.succ
    let z := F (fileCode n) ee
    let q := F ones ![e 0+1,z]
    have hf : F (fileCode (n+1)) e = q+q := by
      rw [modelFileSucc,modelBlock]
    have he : ee (Fin.last n) = p+p := hend
    obtain ⟨t,hr⟩ := ih ee (e 0) (F ones ![v,l+l]+F ones ![v,l+l]+1) he
    refine ⟨((1 : M)+(v+1))+t,?_⟩
    rw [hf]
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,PA194CarryThreeOddFile.cycleThree]
    exact hr
#print axioms carryThreeAcrossExact
end models
end PA194CarryThreeExactFile
