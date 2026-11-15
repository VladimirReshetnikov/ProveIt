import PA194SchedulerFetchPositive
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceFetchLoop
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SchedulerFetchPositive
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem statePC (q : Nat) (args : Fin 11 → M) (tail : M) :
    F pc ![sourceState q args tail] = modelNumeral M q := by
  rw [pcModel]; exact pi₁_pair _ _

theorem stateReg (q : Nat) (args : Fin 11 → M) (tail : M) (r : Fin 9) :
    getSem r.val (pi₂ (sourceState q args tail)) = regsOfArgs args r := by
  change getSem r.val (pi₂ (pair (modelNumeral M q) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  exact packEncodes (regsOfArgs args) tail r

theorem updateRegister (args : Fin 11 → M) (tail m : M) (r : Fin 9) :
    putSem r.val (pack (regsOfArgs args) tail) m =
      pack (regsOfArgs (Function.update args ⟨r.val,by have h := r.isLt; omega⟩ m)) tail := by
  fin_cases r <;> simp [putSem,PA194SourceRegisterRelation.pack,regsOfArgs,pi₁_pair,pi₂_pair,Function.update]

theorem sourceInc (q d : Nat) (r : Fin 9) (hq : q < 3673)
    (hinst : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie q).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc r (some d)))
    (args : Fin 11 → M) (tail : M) :
    F step ![sourceState q args tail] =
      sourceState d (Function.update args ⟨r.val,by have h := r.isLt; omega⟩ (regsOfArgs args r+1)) tail := by
  rw [actualInstructionStep q hq _ (statePC q args tail),hinst]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (sourceState q args tail))
    (F Code.succ (fun _ => getSem r.val (pi₂ (sourceState q args tail))))) = _
  rw [stateReg q args tail r,←modelAddOne]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (pair (modelNumeral M q)
    (pack (regsOfArgs args) tail))) (regsOfArgs args r+1)) = _
  rw [pi₂_pair,updateRegister]
  rfl

theorem sourceJump (q d : Nat) (hq : q < 3673)
    (hinst : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie q).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some d)))
    (args : Fin 11 → M) (tail : M) :
    F step ![sourceState q args tail] = sourceState d args tail := by
  rw [actualInstructionStep q hq _ (statePC q args tail),hinst]
  change pair (modelNumeral M d) (pi₂ (pair (modelNumeral M q) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]; rfl

theorem sourceDecPositive (q d : Nat) (r : Fin 9) (z : Option Nat) (hq : q < 3673)
    (hinst : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie q).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec r z (some d)))
    (args : Fin 11 → M) (tail m : M) (hm : regsOfArgs args r = m+1) :
    F step ![sourceState q args tail] =
      sourceState d (Function.update args ⟨r.val,by have h := r.isLt; omega⟩ m) tail := by
  have hn : getSem r.val (pi₂ (sourceState q args tail)) ≠ (0 : M) := by
    rw [stateReg,hm]
    exact ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m) (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  have hp : F predCode (fun _ => getSem r.val (pi₂ (sourceState q args tail))) = m := by
    rw [stateReg,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  rw [actualInstructionStep q hq _ (statePC q args tail),hinst]
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

theorem inst27 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 27).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 0 (some 31) (some 28)) := by decide +kernel
theorem inst28 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 28).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 8 (some 29)) := by decide +kernel
theorem inst29 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 29).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 30)) := by decide +kernel
theorem inst30 : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 30).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 27)) := by decide +kernel

theorem drainLoop (args : Fin 11 → M) (tail m : M) (hm : args 0 = m+1) :
    let a := Function.update args 0 m
    let b := Function.update a 8 (a 8+1)
    let c := Function.update b 6 (b 6+1)
    F step ![F step ![F step ![F step ![sourceState 27 args tail]]]] = sourceState 27 c tail := by
  let a := Function.update args 0 m
  let b := Function.update a 8 (a 8+1)
  let c := Function.update b 6 (b 6+1)
  have h27 := sourceDecPositive 27 28 0 (some 31) (by decide) inst27 args tail m hm
  have h28 := sourceInc 28 29 8 (by decide) inst28 a tail
  have h29 := sourceInc 29 30 6 (by decide) inst29 b tail
  have h30 := sourceJump 30 27 (by decide) inst30 c tail
  change F step ![sourceState 27 args tail] = sourceState 28 a tail at h27
  change F step ![sourceState 28 a tail] = sourceState 29 b tail at h28
  change F step ![sourceState 29 b tail] = sourceState 30 c tail at h29
  rw [h27,h28,h29,h30]
#print axioms stateReg
#print axioms updateRegister
#print axioms sourceInc
#print axioms sourceJump
#print axioms sourceDecPositive
#print axioms drainLoop
end models
end PA194SourceFetchLoop
