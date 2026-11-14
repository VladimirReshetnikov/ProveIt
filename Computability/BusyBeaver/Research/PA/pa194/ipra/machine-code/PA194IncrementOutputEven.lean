import PA194IncrementOutputExact
import PA194SevenIncrementHeader
import PA194IncrementHeaderReturn
import PA194SevenToSixteen
import PA194SeventeenToRootControl
import PA194UnaryRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194IncrementOutputEven
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194IncrementOutputExact PA194ReturnFile PA194ReturnFileMeaning PA194MarkedFile PA194CarryFile PA194SevenIncrementHeader PA194SeventeenToRootControl PA194IncrementHeaderReturn PA194SevenToSixteen PA194RegisterFile PA194ZeroRuns
open BinaryTapeCodes PA194UnaryRuns PA194SixteenScanExit PA194BinaryDouble
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
/-- The returned seven-prefix file always begins with an even block. -/
theorem outputEven (file : Fin 8 → M) (next spare : M) :
    let args : Fin 3 → M := ![next,spare,(0 : M)]
    let ep := replaceLast 7 file (F (markedFile 1) args)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode 1) (replaceLast 1 (fun i => args i.succ) six)
    let result := F block ![next+1,rest]
    ∃ r : M, F (returnCode 7) (Fin.cases result ep) = r+r := by
  dsimp only
  rw [outputExact,modelFileSucc,modelBlock]
  exact ⟨_,rfl⟩
#print axioms outputEven
end models
end PA194IncrementOutputEven
