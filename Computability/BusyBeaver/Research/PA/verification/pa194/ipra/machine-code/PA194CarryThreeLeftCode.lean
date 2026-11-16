import PA194CarryThreeExactFile
import PA194CarryThreeOddFile
import PA194FirstThreePositiveScan
import PA194ScanInvariant
import PA194CarryEntry
import PA194FirstThreeFirstTo42
import PA194State42Boundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CarryThreeLeftCode
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

/-- The physical fold is the existing primitive-recursive carry-file left
code, when started at an odd controller left half. -/
theorem carried_eq_leftCode (n : Nat) (e : Fin (n+1) → M) (v a : M) :
    PA194CarryThreeExactFile.carried n e v (a+a+1) =
      F (leftCode (n+1)) (Fin.cases a (Fin.cases v e)) := by
  induction n generalizing v a with
  | zero =>
    rw [PA194CarryFile.modelLeftSucc,PA194CarryFile.modelLeftZero]
    rfl
  | succ n ih =>
    rw [PA194CarryFile.modelLeftSucc]
    simp only [Fin.cases_zero,Fin.cases_succ]
    change PA194CarryThreeExactFile.carried n (fun i => e i.succ) (e 0)
      (F ones ![v,(a+a+1)+(a+a+1)]+F ones ![v,(a+a+1)+(a+a+1)]+1) = _
    rw [ih,PA194CarryFile.modelLeftSucc,PA194CarryFile.modelLeftSucc]
    simp only [Fin.cases_zero,Fin.cases_succ]
    congr 1
#print axioms carried_eq_leftCode
end models
end PA194CarryThreeLeftCode
