import PA194ReturnFileMeaning
import PA194MarkedFile
import PA194CarryFile
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194IncrementOutputExact
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
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
/-- The increment output retains the seven-prefix values and spare, increases
slot 8, and appends a fresh one-valued spare before the blank suffix. -/
theorem outputExact (file : Fin 8 → M) (next spare : M) :
    let args : Fin 3 → M := ![next,spare,(0 : M)]
    let ep := replaceLast 7 file (F (markedFile 1) args)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode 1) (replaceLast 1 (fun i => args i.succ) six)
    let result := F block ![next+1,rest]
    F (returnCode 7) (Fin.cases result ep) =
    F (fileCode 7) ![file 0,file 1,file 2,file 3,file 4,file 5,file 6,
      F block ![next+1,F block ![spare,F block ![(1 : M),(0 : M)]]]] := by
  dsimp only
  have hs : (((1 : M)+1)+1)+(((1 : M)+1)+1) = F block ![(1 : M),(0 : M)] := modelSpareOne.symm
  rw [hs,modelReturnMeaning]
  have hrest : F (fileCode 1) (replaceLast 1 (fun i : Fin 2 => (![next,spare,(0 : M)] : Fin 3 → M) i.succ)
      (F block ![(1 : M),(0 : M)])) = F block ![spare,F block ![(1 : M),(0 : M)]] := by
    rw [modelFileSucc]
    simp [replaceLast,Fin.snoc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
  rw [hrest]
  congr 1
  funext i
  fin_cases i <;> simp [replaceLast,Fin.snoc]
#print axioms outputExact
end models
end PA194IncrementOutputExact
