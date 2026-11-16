import PA194OnesCommute
import PA194State42Boundary
import PA194PositiveMarkCycle
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFiveSuccCore
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194OnesCommute PA194State42Boundary PA194PositiveMarkCycle
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

/-- For marker positions at least two, the returned file has one leading
zero followed by one; its remaining data may be nonstandard. -/
theorem returnedOddHalf (idx : Nat) (e : Fin (idx+3) → M) (t : M) :
    let j : Fin (idx+4) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode (idx+1)) (Fin.cases (j 0) (fun i => j i.succ.succ))
    ∃ q : M, w = (q+q+1)+(q+q+1) := by
  dsimp only
  rw [modelReturnCodeSucc,modelOnesCommute]
  exact ⟨_,rfl⟩
#print axioms returnedOddHalf
end models
end PA194FirstFiveSuccCore
