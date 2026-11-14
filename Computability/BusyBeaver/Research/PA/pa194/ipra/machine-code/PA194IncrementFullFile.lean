import PA194IncrementOutputExact
import PA194ReturnFileMeaning
import PA194MarkedFile
import PA194CarryFile
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194IncrementFullFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194IncrementOutputExact
open BinaryTapeCodes PA194RegisterFile PA194MarkedFile PA194ReturnFile PA194ReturnFileMeaning PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- Including the returned first physical block, the output is exactly the
complete eleven-block physical file: nine logical-register blocks, retained
spare, appended one-valued spare, and blank suffix. -/
theorem completeFile (k : M) (file : Fin 8 → M) (next spare : M) :
    let args : Fin 3 → M := ![next,spare,(0 : M)]
    let ep := replaceLast 7 file (F (markedFile 1) args)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode 1) (replaceLast 1 (fun i => args i.succ) six)
    let result := F block ![next+1,rest]
    let out := F (returnCode 7) (Fin.cases result ep)
    F block ![k,out] = F (fileCode 11) ![k,file 0,file 1,file 2,file 3,file 4,file 5,file 6,
      next+1,spare,(1 : M),(0 : M)] := by
  dsimp only
  rw [outputExact]
  simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
  rfl
#print axioms completeFile
end models
end PA194IncrementFullFile
