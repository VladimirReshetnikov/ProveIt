import PA194SourceFetchLoop
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceFetchRestoreLoop
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

theorem sourceDecZero (q d : Nat) (r : Fin 9) (p : Option Nat) (hq : q < 3673)
    (hinst : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie q).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec r (some d) p))
    (args : Fin 11 → M) (tail : M) (hz : regsOfArgs args r = (0 : M)) :
    F step ![sourceState q args tail] = sourceState d args tail := by
  have hr : getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) := (stateReg q args tail r).trans hz
  rw [actualInstructionStep q hq _ (statePC q args tail),hinst]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) then _ else _) = _
  rw [if_pos hr]
  change pair (modelNumeral M d) (pi₂ (pair (modelNumeral M q) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]; rfl

theorem inst31 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 31).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 0 (some 32)) := by decide +kernel
theorem inst32 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 32).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 34) (some 33)) := by decide +kernel
theorem inst33 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 33).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 31)) := by decide +kernel

theorem restoreLoop (args : Fin 11 → M) (tail m : M) (hm : args 6 = m+1) :
    let a := Function.update args 0 (args 0+1)
    let b := Function.update a 6 m
    F step ![F step ![F step ![sourceState 31 args tail]]] = sourceState 31 b tail := by
  let a := Function.update args 0 (args 0+1)
  let b := Function.update a 6 m
  have h31 := sourceInc 31 32 0 (by decide) inst31 args tail
  have ha : regsOfArgs a 6 = m+1 := by simp [regsOfArgs,a,hm]
  have h32 := sourceDecPositive 32 33 6 (some 34) (by decide) inst32 a tail m ha
  have h33 := sourceJump 33 31 (by decide) inst33 b tail
  change F step ![sourceState 31 args tail] = sourceState 32 a tail at h31
  change F step ![sourceState 32 a tail] = sourceState 33 b tail at h32
  rw [h31,h32,h33]

theorem restoreExit (args : Fin 11 → M) (tail : M) (hz : args 6 = (0 : M)) :
    let a := Function.update args 0 (args 0+1)
    F step ![F step ![sourceState 31 args tail]] = sourceState 34 a tail := by
  let a := Function.update args 0 (args 0+1)
  have h31 := sourceInc 31 32 0 (by decide) inst31 args tail
  have ha : regsOfArgs a 6 = (0 : M) := by simp [regsOfArgs,a,hz]
  have h32 := sourceDecZero 32 34 6 (some 33) (by decide) inst32 a tail ha
  change F step ![sourceState 31 args tail] = sourceState 32 a tail at h31
  rw [h31,h32]
#print axioms sourceDecZero
#print axioms restoreLoop
#print axioms restoreExit
end models
end PA194SourceFetchRestoreLoop
