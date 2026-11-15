import PA194DispatchTransfers
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DispatchTag
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive PA194SourceFetchLoop PA194SourceFetchRestoreLoop
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem inst48 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 48).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 3 (some 3661) (some 49)) := by decide +kernel
theorem inst49 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 49).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 3 (some 3554) (some 50)) := by decide +kernel

theorem shiftTag (args : Fin 11 → M) (tail : M) (hz : args 3 = (0 : M)) :
    F step ![sourceState 48 args tail] = sourceState 3661 args tail := by
  exact sourceDecZero 48 3661 3 (some 49) (by decide) inst48 args tail hz

theorem mpTag (args : Fin 11 → M) (tail : M) (h1 : args 3 = (1 : M)) :
    F step ![F step ![sourceState 48 args tail]] = sourceState 3554 (Function.update args 3 0) tail := by
  let out := Function.update args 3 (0 : M)
  have h : args 3 = (0 : M)+1 := by simpa only [zero_add] using h1
  have h48 := sourceDecPositive 48 49 3 (some 3661) (by decide) inst48 args tail (0 : M) h
  have hz : regsOfArgs out 3 = (0 : M) := by simp [out,regsOfArgs]
  have h49 := sourceDecZero 49 3554 3 (some 50) (by decide) inst49 out tail hz
  change F step ![sourceState 48 args tail] = sourceState 49 out tail at h48
  rw [h48,h49]

theorem axTag (args : Fin 11 → M) (tail c : M) (hc : args 3 = (c+1)+1) :
    F step ![F step ![sourceState 48 args tail]] = sourceState 50 (Function.update args 3 c) tail := by
  let mid := Function.update args 3 (c+1)
  let out := Function.update mid 3 c
  have h48 := sourceDecPositive 48 49 3 (some 3661) (by decide) inst48 args tail (c+1) hc
  have hm : regsOfArgs mid 3 = c+1 := by simp [mid,regsOfArgs]
  have h49 := sourceDecPositive 49 50 3 (some 3554) (by decide) inst49 mid tail c hm
  change F step ![sourceState 48 args tail] = sourceState 49 mid tail at h48
  change F step ![sourceState 49 mid tail] = sourceState 50 out tail at h49
  rw [h48,h49]
  simp [out,mid,Function.update_idem]
#print axioms shiftTag
#print axioms mpTag
#print axioms axTag
end models
end PA194DispatchTag
