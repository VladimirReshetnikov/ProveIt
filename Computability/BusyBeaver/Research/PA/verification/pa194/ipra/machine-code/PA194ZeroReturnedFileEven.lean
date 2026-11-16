import PA194RollbackCell
import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroReturnedFileEven
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAExhaustion PA194RollbackCell PA194BinaryDouble
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
open PA194ReturnedDecrement PA194MarkedFile PA194CarryFile PA194ReturnFile
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
/-- The zero-selected decrement output remains an ordinary even-coded file. -/
theorem returnedZeroEven (idx n : Nat) (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) :
    let tail := F (fileCode (n+1)) rest
    let ep := replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F markedBlock ![(0 : M),tail])
    let file := F (returnCode idx) (Fin.cases (F block ![(0 : M),tail]) ep)
    ∃ r : M, file = r+r := by
  dsimp only
  rw [returnedUpdatedFile]
  cases idx with
  | zero =>
      rw [fileCode,modelProjection]
      simp only [replaceLast,Fin.snoc]
      rw [modelBlock]
      exact ⟨_,rfl⟩
  | succ idx =>
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
#print axioms returnedZeroEven
end models
end PA194ZeroReturnedFileEven
