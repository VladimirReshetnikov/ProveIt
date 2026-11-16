import PA194SourceFetchRestoreLoop

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PA194ShiftModelHalt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194SourceFetchRestoreLoop PA194SourceControllerStep PA194IteratedSimulation


private theorem inst3661 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3661).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 1 (some 3664) (some 3662)) := by decide +kernel

private theorem inst3662 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3662).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 3663)) := by decide +kernel

private theorem inst3663 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3663).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3661)) := by decide +kernel

private theorem inst3664 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3664).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 5 (some 3668) (some 3665)) := by decide +kernel

private theorem inst3665 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3665).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 1 (some 3666)) := by decide +kernel

private theorem inst3666 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3666).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 3667)) := by decide +kernel

private theorem inst3667 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3667).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3664)) := by decide +kernel

private theorem inst3668 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3668).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3671) (some 3669)) := by decide +kernel

private theorem inst3669 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3669).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 5 (some 3670)) := by decide +kernel

private theorem inst3670 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3670).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3668)) := by decide +kernel

private theorem inst3671 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3671).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 3672)) := by decide +kernel

private theorem inst3672 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 3672).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 0)) := by decide +kernel

private theorem inst0 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 0).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 5 (some 4) (some 1)) := by decide +kernel

private theorem inst1 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 1).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3) (some 2)) := by decide +kernel

private theorem inst2 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 2).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 0)) := by decide +kernel

private theorem inst4 :
    (M6.Source.PathTrie.nthSite PA194.SourceTree.trie 4).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 10) (some 5)) := by decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A finite number of source instructions, evaluated over the model. -/
private def advance (next : M → M) : Nat → M → M
  | 0, state => state
  | n+1, state => next (advance next n state)

private theorem advance_run (n : Nat) (seed : M) :
    advance (fun s => F step ![s]) n seed =
      F run ![modelNumeral M n,seed] := by
  induction n with
  | zero => exact (iterateZero step seed).symm
  | succ n ih =>
    rw [advance,ih]
    change F step ![F (iterate step) ![modelNumeral M n,seed]] =
      F (iterate step) ![modelNumeral M (n+1),seed]
    rw [PA194FiniteControls.modelNumeralSucc, iterateSucc]

private theorem haltAt10 (args : Fin 11 → M) (tail : M) :
    F step ![sourceState 10 args tail] = sourceState 3674 args tail := by
  rw [site10Step _ (statePC 10 args tail)]
  change pair (modelNumeral M 3674) (pi₂ (pair (modelNumeral M 10) _)) = _
  rw [pi₂_pair]
  rfl

theorem halts_top_one (args : Fin 11 → M) (tail : M)
    (ht : args 1 = 1) (hh : args 5 = 0) (hx : args 6 = 0) :
    F pc ![F run ![modelNumeral M 17,sourceState 3661 args tail]] =
      modelNumeral M 3674 := by
  have check1 : regsOfArgs args 1 = (0 : M)+1 := by
    change args 1 = _
    simp [ht,hh,hx]
  let a1 := Function.update args 1 (0 : M)
  have step1 : F step ![sourceState 3661 args tail] = sourceState 3662 a1 tail :=
    sourceDecPositive 3661 3662 1 (some 3664) (by decide) inst3661 args tail 0 check1
  let a2 := Function.update a1 6 (a1 6+1)
  have step2 : F step ![sourceState 3662 a1 tail] = sourceState 3663 a2 tail :=
    sourceInc 3662 3663 6 (by decide) inst3662 a1 tail
  have step3 := sourceJump 3663 3661 (by decide) inst3663 a2 tail
  have check4 : regsOfArgs a2 1 = 0 := by
    change a2 1 = _
    simp [ht,hh,hx,a1,a2]
  have step4 := sourceDecZero 3661 3664 1 (some 3662) (by decide) inst3661 a2 tail check4
  have check5 : regsOfArgs a2 5 = 0 := by
    change a2 5 = _
    simp [ht,hh,hx,a1,a2]
  have step5 := sourceDecZero 3664 3668 5 (some 3665) (by decide) inst3664 a2 tail check5
  have check6 : regsOfArgs a2 6 = (0 : M)+1 := by
    change a2 6 = _
    simp [ht,hh,hx,a1,a2]
  let a6 := Function.update a2 6 (0 : M)
  have step6 : F step ![sourceState 3668 a2 tail] = sourceState 3669 a6 tail :=
    sourceDecPositive 3668 3669 6 (some 3671) (by decide) inst3668 a2 tail 0 check6
  let a7 := Function.update a6 5 (a6 5+1)
  have step7 : F step ![sourceState 3669 a6 tail] = sourceState 3670 a7 tail :=
    sourceInc 3669 3670 5 (by decide) inst3669 a6 tail
  have step8 := sourceJump 3670 3668 (by decide) inst3670 a7 tail
  have check9 : regsOfArgs a7 6 = 0 := by
    change a7 6 = _
    simp [ht,hh,hx,a1,a2,a6,a7]
  have step9 := sourceDecZero 3668 3671 6 (some 3669) (by decide) inst3668 a7 tail check9
  let a10 := Function.update a7 6 (a7 6+1)
  have step10 : F step ![sourceState 3671 a7 tail] = sourceState 3672 a10 tail :=
    sourceInc 3671 3672 6 (by decide) inst3671 a7 tail
  have step11 := sourceJump 3672 0 (by decide) inst3672 a10 tail
  have check12 : regsOfArgs a10 5 = (0 : M)+1 := by
    change a10 5 = _
    simp [ht,hh,hx,a1,a2,a6,a7,a10]
  let a12 := Function.update a10 5 (0 : M)
  have step12 : F step ![sourceState 0 a10 tail] = sourceState 1 a12 tail :=
    sourceDecPositive 0 1 5 (some 4) (by decide) inst0 a10 tail 0 check12
  have check13 : regsOfArgs a12 6 = (0 : M)+1 := by
    change a12 6 = _
    simp [ht,hh,hx,a1,a2,a6,a7,a10,a12]
  let a13 := Function.update a12 6 (0 : M)
  have step13 : F step ![sourceState 1 a12 tail] = sourceState 2 a13 tail :=
    sourceDecPositive 1 2 6 (some 3) (by decide) inst1 a12 tail 0 check13
  have step14 := sourceJump 2 0 (by decide) inst2 a13 tail
  have check15 : regsOfArgs a13 5 = 0 := by
    change a13 5 = _
    simp [ht,hh,hx,a1,a2,a6,a7,a10,a12,a13]
  have step15 := sourceDecZero 0 4 5 (some 1) (by decide) inst0 a13 tail check15
  have check16 : regsOfArgs a13 6 = 0 := by
    change a13 6 = _
    simp [ht,hh,hx,a1,a2,a6,a7,a10,a12,a13]
  have step16 := sourceDecZero 4 10 6 (some 5) (by decide) inst4 a13 tail check16
  rw [←advance_run]
  simp only [advance]
  rw [step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12,step13,step14,step15,step16,haltAt10]
  exact statePC 3674 a13 tail

theorem halts_cache_one (args : Fin 11 → M) (tail : M)
    (ht : args 1 = 0) (hh : args 5 = 1) (hx : args 6 = 0) :
    F pc ![F run ![modelNumeral M 18,sourceState 3661 args tail]] =
      modelNumeral M 3674 := by
  have check1 : regsOfArgs args 1 = 0 := by
    change args 1 = _
    simp [ht,hh,hx]
  have step1 := sourceDecZero 3661 3664 1 (some 3662) (by decide) inst3661 args tail check1
  have check2 : regsOfArgs args 5 = (0 : M)+1 := by
    change args 5 = _
    simp [ht,hh,hx]
  let a2 := Function.update args 5 (0 : M)
  have step2 : F step ![sourceState 3664 args tail] = sourceState 3665 a2 tail :=
    sourceDecPositive 3664 3665 5 (some 3668) (by decide) inst3664 args tail 0 check2
  let a3 := Function.update a2 1 (a2 1+1)
  have step3 : F step ![sourceState 3665 a2 tail] = sourceState 3666 a3 tail :=
    sourceInc 3665 3666 1 (by decide) inst3665 a2 tail
  let a4 := Function.update a3 6 (a3 6+1)
  have step4 : F step ![sourceState 3666 a3 tail] = sourceState 3667 a4 tail :=
    sourceInc 3666 3667 6 (by decide) inst3666 a3 tail
  have step5 := sourceJump 3667 3664 (by decide) inst3667 a4 tail
  have check6 : regsOfArgs a4 5 = 0 := by
    change a4 5 = _
    simp [ht,hh,hx,a2,a3,a4]
  have step6 := sourceDecZero 3664 3668 5 (some 3665) (by decide) inst3664 a4 tail check6
  have check7 : regsOfArgs a4 6 = (0 : M)+1 := by
    change a4 6 = _
    simp [ht,hh,hx,a2,a3,a4]
  let a7 := Function.update a4 6 (0 : M)
  have step7 : F step ![sourceState 3668 a4 tail] = sourceState 3669 a7 tail :=
    sourceDecPositive 3668 3669 6 (some 3671) (by decide) inst3668 a4 tail 0 check7
  let a8 := Function.update a7 5 (a7 5+1)
  have step8 : F step ![sourceState 3669 a7 tail] = sourceState 3670 a8 tail :=
    sourceInc 3669 3670 5 (by decide) inst3669 a7 tail
  have step9 := sourceJump 3670 3668 (by decide) inst3670 a8 tail
  have check10 : regsOfArgs a8 6 = 0 := by
    change a8 6 = _
    simp [ht,hh,hx,a2,a3,a4,a7,a8]
  have step10 := sourceDecZero 3668 3671 6 (some 3669) (by decide) inst3668 a8 tail check10
  let a11 := Function.update a8 6 (a8 6+1)
  have step11 : F step ![sourceState 3671 a8 tail] = sourceState 3672 a11 tail :=
    sourceInc 3671 3672 6 (by decide) inst3671 a8 tail
  have step12 := sourceJump 3672 0 (by decide) inst3672 a11 tail
  have check13 : regsOfArgs a11 5 = (0 : M)+1 := by
    change a11 5 = _
    simp [ht,hh,hx,a2,a3,a4,a7,a8,a11]
  let a13 := Function.update a11 5 (0 : M)
  have step13 : F step ![sourceState 0 a11 tail] = sourceState 1 a13 tail :=
    sourceDecPositive 0 1 5 (some 4) (by decide) inst0 a11 tail 0 check13
  have check14 : regsOfArgs a13 6 = (0 : M)+1 := by
    change a13 6 = _
    simp [ht,hh,hx,a2,a3,a4,a7,a8,a11,a13]
  let a14 := Function.update a13 6 (0 : M)
  have step14 : F step ![sourceState 1 a13 tail] = sourceState 2 a14 tail :=
    sourceDecPositive 1 2 6 (some 3) (by decide) inst1 a13 tail 0 check14
  have step15 := sourceJump 2 0 (by decide) inst2 a14 tail
  have check16 : regsOfArgs a14 5 = 0 := by
    change a14 5 = _
    simp [ht,hh,hx,a2,a3,a4,a7,a8,a11,a13,a14]
  have step16 := sourceDecZero 0 4 5 (some 1) (by decide) inst0 a14 tail check16
  have check17 : regsOfArgs a14 6 = 0 := by
    change a14 6 = _
    simp [ht,hh,hx,a2,a3,a4,a7,a8,a11,a13,a14]
  have step17 := sourceDecZero 4 10 6 (some 5) (by decide) inst4 a14 tail check17
  rw [←advance_run]
  simp only [advance]
  rw [step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12,step13,step14,step15,step16,step17,haltAt10]
  exact statePC 3674 a14 tail

/-- The SHIFT guard halts from site 3661 when the top and cache add to one. -/
theorem halt_of_sum_one (args : Fin 11 → M) (tail : M)
    (hs : args 1 + args 5 = (1 : M)) (hx : args 6 = 0) :
    ∃ n : M, F pc ![F run ![n,sourceState 3661 args tail]] = modelNumeral M 3674 := by
  rcases zero_or_succ (args 1) with ht | ⟨t, ht⟩
  · have hh : args 5 = 1 := by simpa only [ht,zero_add] using hs
    exact ⟨_, halts_cache_one args tail ht hh hx⟩
  · have hzero : t + args 5 = 0 := by
      apply add_right_cancel (b := (1 : M))
      simpa [ht,add_assoc,add_comm,add_left_comm] using hs
    have hle := add_le_add_left (zero_le : (0 : M) ≤ args 5) t
    have ht0 : t = 0 := le_antisymm (by simpa only [zero_add,add_comm (args 5) t,hzero] using hle) zero_le
    have hh : args 5 = 0 := by simpa only [ht0,zero_add] using hzero
    exact ⟨_, halts_top_one args tail (by simp only [ht,ht0,zero_add]) hh hx⟩

#print axioms halts_top_one
#print axioms halts_cache_one
#print axioms halt_of_sum_one
end models
end PA194ShiftModelHalt
