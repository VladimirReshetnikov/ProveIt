import PA194UnpairDrainComplete
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194Transfer45Loop
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SchedulerFetchPositive PA194SourceFetchLoop PA194SourceFetchRestoreLoop
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem inst45 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 45).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 48) (some 46)) := by decide +kernel
theorem inst46 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 46).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 3 (some 47)) := by decide +kernel
theorem inst47 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 47).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 45)) := by decide +kernel

theorem transferLoop (args : Fin 11 → M) (tail m : M) (hm : args 6 = m+1) :
    let a := Function.update args 6 m
    let b := Function.update a 3 (a 3+1)
    F step ![F step ![F step ![sourceState 45 args tail]]] = sourceState 45 b tail := by
  let a := Function.update args 6 m
  let b := Function.update a 3 (a 3+1)
  have h45 := sourceDecPositive 45 46 6 (some 48) (by decide) inst45 args tail m hm
  have h46 := sourceInc 46 47 3 (by decide) inst46 a tail
  have h47 := sourceJump 47 45 (by decide) inst47 b tail
  change F step ![sourceState 45 args tail] = sourceState 46 a tail at h45
  change F step ![sourceState 46 a tail] = sourceState 47 b tail at h46
  rw [h45,h46,h47]

theorem transferExit (args : Fin 11 → M) (tail : M) (hz : args 6 = (0 : M)) :
    F step ![sourceState 45 args tail] = sourceState 48 args tail := by
  exact sourceDecZero 45 48 6 (some 46) (by decide) inst45 args tail hz
#print axioms transferLoop
#print axioms transferExit
end models
end PA194Transfer45Loop
