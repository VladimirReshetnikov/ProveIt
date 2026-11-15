import PA194UnpairDrainComplete
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194Transfer42Loop
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

theorem inst42 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 42).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 45) (some 43)) := by decide +kernel
theorem inst43 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 43).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 8 (some 44)) := by decide +kernel
theorem inst44 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 44).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 42)) := by decide +kernel

theorem transferLoop (args : Fin 11 → M) (tail m : M) (hm : args 7 = m+1) :
    let a := Function.update args 7 m
    let b := Function.update a 8 (a 8+1)
    F step ![F step ![F step ![sourceState 42 args tail]]] = sourceState 42 b tail := by
  let a := Function.update args 7 m
  let b := Function.update a 8 (a 8+1)
  have h42 := sourceDecPositive 42 43 7 (some 45) (by decide) inst42 args tail m hm
  have h43 := sourceInc 43 44 8 (by decide) inst43 a tail
  have h44 := sourceJump 44 42 (by decide) inst44 b tail
  change F step ![sourceState 42 args tail] = sourceState 43 a tail at h42
  change F step ![sourceState 43 a tail] = sourceState 44 b tail at h43
  rw [h42,h43,h44]

theorem transferExit (args : Fin 11 → M) (tail : M) (hz : args 7 = (0 : M)) :
    F step ![sourceState 42 args tail] = sourceState 45 args tail := by
  exact sourceDecZero 42 45 7 (some 43) (by decide) inst42 args tail hz
#print axioms transferLoop
#print axioms transferExit
end models
end PA194Transfer42Loop
