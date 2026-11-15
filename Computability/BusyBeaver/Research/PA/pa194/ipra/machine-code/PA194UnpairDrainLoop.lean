import PA194UnpairRound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194UnpairDrainLoop
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SchedulerFetchPositive PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194UnpairRound
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem inst38 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 38).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 41) (some 39)) := by decide +kernel
theorem inst39 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 39).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 40)) := by decide +kernel
theorem inst40 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 40).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 38)) := by decide +kernel

theorem drainLoop (args : Fin 11 → M) (tail m : M) (hm : args 7 = m+1) :
    let a := Function.update args 7 m
    let b := Function.update a 6 (a 6+1)
    F step ![F step ![F step ![sourceState 38 args tail]]] = sourceState 38 b tail := by
  let a := Function.update args 7 m
  let b := Function.update a 6 (a 6+1)
  have h38 := sourceDecPositive 38 39 7 (some 41) (by decide) inst38 args tail m hm
  have h39 := sourceInc 39 40 6 (by decide) inst39 a tail
  have h40 := sourceJump 40 38 (by decide) inst40 b tail
  change F step ![sourceState 38 args tail] = sourceState 39 a tail at h38
  change F step ![sourceState 39 a tail] = sourceState 40 b tail at h39
  rw [h38,h39,h40]

theorem drainExit (args : Fin 11 → M) (tail : M) (hz : args 7 = (0 : M)) :
    F step ![F step ![sourceState 38 args tail]] = sourceState 34 args tail := by
  have h38 := sourceDecZero 38 41 7 (some 39) (by decide) inst38 args tail hz
  have h41 := sourceJump 41 34 (by decide) inst41 args tail
  rw [h38,h41]
#print axioms drainLoop
#print axioms drainExit
end models
end PA194UnpairDrainLoop
