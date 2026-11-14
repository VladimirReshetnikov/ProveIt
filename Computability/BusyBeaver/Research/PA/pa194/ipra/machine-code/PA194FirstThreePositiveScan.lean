import PA194ScanInvariant
import PA194CarryEntry
import PA194FirstThreeFirstTo42
import PA194State42Boundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstThreePositiveScan
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

/-- Scan the successor-selected residual run and enter dense 3 on
the following file block. -/
theorem scanTo3 (k l p : M) :
    let a := F ones ![k,l]
    F PA194Stepper.stepper ![k+1,
      F pairCode ![modelNumeral M 1,F pairCode ![l,F ones ![k,p+p]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![a+a+1,p]] := by
  dsimp only
  have hs := PA194ScanInvariant.modelFullScan k l (p+p)
  rw [←modelNumeralOne] at hs
  change F PA194Stepper.stepper ![F addCode ![k,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,modelPackedCarryOne]
#print axioms scanTo3
end models
end PA194FirstThreePositiveScan
