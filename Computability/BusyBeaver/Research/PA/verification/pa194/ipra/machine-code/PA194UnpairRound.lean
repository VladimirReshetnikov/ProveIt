import PA194SourceFetchRestoreLoop
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194UnpairRound
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

theorem inst34 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 34).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 8 (some 42) (some 35)) := by decide +kernel
theorem inst35 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 35).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 36)) := by decide +kernel
theorem inst36 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 36).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 38) (some 37)) := by decide +kernel
theorem inst37 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 37).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 41)) := by decide +kernel
theorem inst41 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 41).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 34)) := by decide +kernel

theorem positiveRound (args : Fin 11 → M) (tail w a : M)
    (hw : args 8 = w+1) (ha : args 6 = a+1) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := Function.update a2 6 a
    F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
        F PA194SourceControllerCode.step ![sourceState 34 args tail]]]]] = sourceState 34 out tail ∧
    out 8 + out 7 = args 8 + args 7 ∧ out 6 + out 7 = args 6 + args 7 ∧
    ∀ i : Fin 11, i ≠ 6 → i ≠ 7 → i ≠ 8 → out i = args i := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := Function.update a2 6 a
  have h34 := sourceDecPositive 34 35 8 (some 42) (by decide) inst34 args tail w hw
  have h35 := sourceInc 35 36 7 (by decide) inst35 a1 tail
  have ha2 : regsOfArgs a2 6 = a+1 := by simp [regsOfArgs,a2,a1,ha]
  have h36 := sourceDecPositive 36 37 6 (some 38) (by decide) inst36 a2 tail a ha2
  have h37 := sourceJump 37 41 (by decide) inst37 out tail
  have h41 := sourceJump 41 34 (by decide) inst41 out tail
  change F PA194SourceControllerCode.step ![sourceState 34 args tail] = sourceState 35 a1 tail at h34
  change F PA194SourceControllerCode.step ![sourceState 35 a1 tail] = sourceState 36 a2 tail at h35
  change F PA194SourceControllerCode.step ![sourceState 36 a2 tail] = sourceState 37 out tail at h36
  refine ⟨?_,?_,?_,?_⟩
  · rw [h34,h35,h36,h37,h41]
  · simp [out,a2,a1,hw,add_assoc,add_comm,add_left_comm]
  · simp [out,a2,a1,ha,add_assoc,add_comm,add_left_comm]
  · intro i h6 h7 h8
    simp [out,a2,a1,Function.update_of_ne h6,Function.update_of_ne h7,Function.update_of_ne h8]
#print axioms positiveRound
end models
end PA194UnpairRound
