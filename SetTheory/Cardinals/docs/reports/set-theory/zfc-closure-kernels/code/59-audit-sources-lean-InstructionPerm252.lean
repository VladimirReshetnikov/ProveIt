import BusyBeaver.ZFC.Permutation252Simulation

/-!
One complete logical instruction of the permutation252 machine.

This composes the actual binary site checker with the whole-tape framing
adapters. The source instruction, register semantics, and proof strategy
derive from Mira-Cult, Jeff, and Wade's framework, as attributed in SitePerm252.
Every successful logical step has a strictly positive number of binary moves.
The theorem is conditional on an accepted site; decoder coverage is separate.
-/

namespace SetTheory.BusyBeaver.ZFC.InstructionPerm252

open RegisterPath Permutation252Frame SymbolicPerm252
open SitePerm252 Permutation252Simulation

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem incRev_length (P : List Bool) : (incRev P).length = P.length := by
  induction P with
  | nil => rfl
  | cons b P ih => cases b <;> simp [incRev, ih]

theorem incPath_length (P : List Bool) : (incPath P).length = P.length := by
  simp only [incPath, List.length_reverse, incRev_length]

theorem stripPath_length (b : Bool) (k : Nat) (P : List Bool) :
    (stripPath b k P).length ≤ P.length := by
  obtain ⟨T, ht⟩ := RegisterPathClean.stripPath_prefix b k P
  have hl := congrArg List.length ht
  simp only [List.length_append] at hl
  omega

theorem breakPath_length (k : Nat) (P : List Bool) :
    (breakPath k P).length ≤ P.length := by
  simpa only [breakPath, incPath_length] using stripPath_length false k P

theorem continuePath_length (k : Nat) (P : List Bool) :
    (continuePath k P).length ≤ P.length := stripPath_length true k P

/-- Every accepted nonhalting site updates the complete dispatch frame.
The physical spare suffix is retained; positive decrement appends one zero. -/
theorem execute_frame (Q : List Bool) (e : Edge) (R : Registers)
    (spares : List Nat) (n : Nat) (binary : Config 252) (next : Configuration)
    (hcheck : checkSite Q e = true) (htail : LogicalTailZero R)
    (hc : Represents n (vregs R ++ spares) (start Q) binary)
    (he : execute e Q R = some next) :
    ∃ k : Nat, 0 < k ∧ ∃ gap spares',
      DispatchFrame dispatch (machinePerm252.runFrom binary k) next gap spares' := by
  have hlen : Q.length ≤ 40 := checkSite_length Q e hcheck
  cases e with
  | node r => simp only [execute, reduceCtorEq] at he
  | halt => simp only [execute, reduceCtorEq] at he
  | inc r =>
    have hr := check_inc_bound Q r hcheck
    simp only [execute, Option.some.injEq] at he
    subst next
    obtain ⟨k, hk, hs⟩ := runTo_sound none Q _ (check_inc Q r hr hcheck)
      n _ (valid_none R spares) binary hc
    refine ⟨k, hk, n + (40 + (if allOnes Q then 1 else 0) - (incPath Q).length), spares, ?_⟩
    exact target_frame n _ (incPath Q) (allOnes Q) _
      (update R r (R r + 1)) spares _
      (by rw [incPath_length]; omega) (tail_update R r _ hr htail)
      (increment_rebase R spares r hr) hs
  | decnz r =>
    have hr := check_decnz_bound Q r hcheck
    obtain ⟨hzero, hpositive⟩ := check_decnz Q r hr hcheck
    cases hv : R r with
    | zero =>
      simp only [execute, hv, Option.some.injEq] at he
      subst next
      obtain ⟨k, hk, hs⟩ := runTo_sound _ Q _ hzero n _
        (valid_branch R spares r hr true hv) binary hc
      refine ⟨k, hk, n + (40 + (if allOnes (stripPath false 1 Q) then 1 else 0) -
        (breakPath 1 Q).length), spares, ?_⟩
      exact target_frame n _ (breakPath 1 Q) (allOnes (stripPath false 1 Q)) _
        R spares _ (by have := breakPath_length 1 Q; omega) htail
        (unchanged_rebase R spares) hs
    | succ v =>
      simp only [execute, hv, Option.some.injEq] at he
      subst next
      obtain ⟨k, hk, hs⟩ := runTo_sound _ Q _ hpositive n _
        (valid_branch R spares r hr false (by simp [hv])) binary hc
      refine ⟨k, hk, n + (40 + (if allOnes Q then 1 else 0) - (incPath Q).length),
        spares ++ [0], ?_⟩
      have hb := decrement_rebase R spares r hr
      simp only [hv, Nat.add_sub_cancel] at hb
      exact target_frame n _ (incPath Q) (allOnes Q) _ (update R r v)
        (spares ++ [0]) _ (by rw [incPath_length]; omega)
        (tail_update R r _ hr htail) hb hs
  | brk k =>
    simp only [execute, Option.some.injEq] at he
    subst next
    obtain ⟨t, ht, hs⟩ := runTo_sound none Q _ (check_break Q k hcheck)
      n _ (valid_none R spares) binary hc
    refine ⟨t, ht, n + (40 + (if allOnes (stripPath false k Q) then 1 else 0) -
      (breakPath k Q).length), spares, ?_⟩
    exact target_frame n _ (breakPath k Q) (allOnes (stripPath false k Q)) _
      R spares _ (by have := breakPath_length k Q; omega) htail
      (unchanged_rebase R spares) hs
  | cont k =>
    simp only [execute, Option.some.injEq] at he
    subst next
    obtain ⟨t, ht, hs⟩ := runTo_sound none Q _ (check_continue Q k hcheck)
      n _ (valid_none R spares) binary hc
    refine ⟨t, ht, n + (40 - (continuePath k Q).length), spares, ?_⟩
    exact target_frame n _ (continuePath k Q) false _ R spares _
      (by have := continuePath_length k Q; simp only [Bool.false_eq_true, if_false]; omega)
      htail (unchanged_rebase R spares) hs

theorem halt_frame (Q : List Bool) (R : Registers) (spares : List Nat)
    (n : Nat) (binary : Config 252) (hcheck : checkSite Q .halt = true)
    (hc : Represents n (vregs R ++ spares) (start Q) binary) :
    ∃ k : Nat, 0 < k ∧ (machinePerm252.runFrom binary k).state = none :=
  runHalt_sound Q (check_halt Q hcheck) n _ (valid_none R spares).1 binary hc

#print axioms execute_frame
#print axioms halt_frame

end SetTheory.BusyBeaver.ZFC.InstructionPerm252
