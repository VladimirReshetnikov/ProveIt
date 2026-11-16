import PA194AX11HSource
import PA194SourceFetchRestoreLoop
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194AX11HSourceAt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SchedulerFetchPositive PA194SourceFetchLoop
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem sourceInc (q d : Nat) (r : Fin 9) (hq : q < 3671)
    (hinst : (PA194AX11HSource.program[q]'(by simpa [PA194AX11HSource.program_length] using hq)) = some (.inc r (some d)))
    (args : Fin 11 → M) (tail : M) :
    F PA194AX11HSource.step ![sourceState q args tail] =
      sourceState d (Function.update args ⟨r.val,by have h := r.isLt; omega⟩ (regsOfArgs args r+1)) tail := by
  rw [PA194AX11HSource.selected q hq _ (statePC q args tail),hinst]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (sourceState q args tail))
    (F Code.succ (fun _ => getSem r.val (pi₂ (sourceState q args tail))))) = _
  rw [stateReg q args tail r,←modelAddOne]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (pair (modelNumeral M q)
    (pack (regsOfArgs args) tail))) (regsOfArgs args r+1)) = _
  rw [pi₂_pair,updateRegister]
  rfl


theorem sourceJump (q d : Nat) (hq : q < 3671)
    (hinst : (PA194AX11HSource.program[q]'(by simpa [PA194AX11HSource.program_length] using hq)) = some (.jump (some d)))
    (args : Fin 11 → M) (tail : M) :
    F PA194AX11HSource.step ![sourceState q args tail] = sourceState d args tail := by
  rw [PA194AX11HSource.selected q hq _ (statePC q args tail),hinst]
  change pair (modelNumeral M d) (pi₂ (pair (modelNumeral M q) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]; rfl


theorem sourceDecPositive (q d : Nat) (r : Fin 9) (z : Option Nat) (hq : q < 3671)
    (hinst : (PA194AX11HSource.program[q]'(by simpa [PA194AX11HSource.program_length] using hq)) = some (.dec r z (some d)))
    (args : Fin 11 → M) (tail m : M) (hm : regsOfArgs args r = m+1) :
    F PA194AX11HSource.step ![sourceState q args tail] =
      sourceState d (Function.update args ⟨r.val,by have h := r.isLt; omega⟩ m) tail := by
  have hn : getSem r.val (pi₂ (sourceState q args tail)) ≠ (0 : M) := by
    rw [stateReg,hm]
    exact ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m) (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  have hp : F predCode (fun _ => getSem r.val (pi₂ (sourceState q args tail))) = m := by
    rw [stateReg,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  rw [PA194AX11HSource.selected q hq _ (statePC q args tail),hinst]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) then _ else _) = _
  rw [if_neg hn]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (sourceState q args tail))
      (F predCode (fun _ => getSem r.val (pi₂ (sourceState q args tail))))) = _
  rw [hp]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (pair (modelNumeral M q)
    (pack (regsOfArgs args) tail))) m) = _
  rw [pi₂_pair,updateRegister]
  rfl


theorem sourceDecZero (q d : Nat) (r : Fin 9) (p : Option Nat) (hq : q < 3671)
    (hinst : (PA194AX11HSource.program[q]'(by simpa [PA194AX11HSource.program_length] using hq)) = some (.dec r (some d) p))
    (args : Fin 11 → M) (tail : M) (hz : regsOfArgs args r = (0 : M)) :
    F PA194AX11HSource.step ![sourceState q args tail] = sourceState d args tail := by
  have hr : getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) := (stateReg q args tail r).trans hz
  rw [PA194AX11HSource.selected q hq _ (statePC q args tail),hinst]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) then _ else _) = _
  rw [if_pos hr]
  change pair (modelNumeral M d) (pi₂ (pair (modelNumeral M q) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]; rfl

#print axioms sourceInc
#print axioms sourceJump
#print axioms sourceDecPositive
#print axioms sourceDecZero
end models
end PA194AX11HSourceAt
