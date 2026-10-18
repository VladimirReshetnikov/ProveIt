import BusyBeaver.ZFC.Routing245Simulation

/-!
One complete logical instruction of the routing245 machine.

This composes the actual site checker with the scoped DispatchFrame64
adapters. Mira-Cult and Jeff's original machine verification and Wade's path
semantics retain the attribution given in SiteRouting245.

Every accepted nonhalting site implements the logical step with a strictly
positive number of actual binary moves, preserves a nonempty spare suffix,
and returns the whole infinite tape in a 64-cell dispatch frame. Increment
appends a value-one spare; positive decrement preserves the suffix and adds
one gap cell. Register values, gap parameters and spare values are arbitrary.
The accepted-site premise is explicit; full decoder coverage is separate.
-/

namespace SetTheory.BusyBeaver.ZFC.InstructionRouting245

open RegisterPath Permutation252Frame SymbolicRouting245
open SiteRouting245 Routing245Simulation

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
The spare suffix stays nonempty. Increment appends one value-one block;
positive decrement preserves the suffix and adds one gap cell. -/
theorem execute_frame (Q : List Bool) (e : Edge) (R : Registers)
    (spares : List Nat) (n : Nat) (binary : Config 245) (next : Configuration)
    (hcheck : checkSite Q e = true) (htail : LogicalTailZero R)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary)
    (he : execute e Q R = some next) :
    ∃ k : Nat, 0 < k ∧ ∃ gap spares', spares' ≠ [] ∧
      DispatchFrame64 dispatch (machineRouting245.runFrom binary k) next gap spares' := by
  have hlen : Q.length ≤ 64 := checkSite_length Q e hcheck
  cases e with
  | node r => simp only [execute, reduceCtorEq] at he
  | halt => simp only [execute, reduceCtorEq] at he
  | inc r =>
    have hr := check_inc_bound Q r hcheck
    simp only [execute, Option.some.injEq] at he
    subst next
    obtain ⟨k, hk, hs⟩ := runTo_sound none Q _ (check_inc Q r hr hcheck)
      n _ (valid_none R spares hspares) binary hc
    refine ⟨k, hk, n + (64 + (if allOnes Q then 1 else 0) - (incPath Q).length), spares ++ [1], by simp, ?_⟩
    exact target_frame n _ (incPath Q) (allOnes Q) 0 _
      (update R r (R r + 1)) (spares ++ [1]) _
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
        (valid_branch R spares hspares r hr true hv) binary hc
      refine ⟨k, hk, n + (64 + (if allOnes (stripPath false 1 Q) then 1 else 0) -
        (breakPath 1 Q).length), spares, hspares, ?_⟩
      exact target_frame n _ (breakPath 1 Q) (allOnes (stripPath false 1 Q)) 0 _
        R spares _ (by have := breakPath_length 1 Q; omega) htail
        (unchanged_rebase R spares) hs
    | succ v =>
      simp only [execute, hv, Option.some.injEq] at he
      subst next
      obtain ⟨k, hk, hs⟩ := runTo_sound _ Q _ hpositive n _
        (valid_branch R spares hspares r hr false (by simp [hv])) binary hc
      refine ⟨k, hk, n + (64 + (if allOnes Q then 1 else 0) + 1 - (incPath Q).length),
        spares, hspares, ?_⟩
      have hb := decrement_rebase R spares r hr
      simp only [hv, Nat.add_sub_cancel] at hb
      exact target_frame n _ (incPath Q) (allOnes Q) 1 _ (update R r v)
        spares _ (by rw [incPath_length]; omega)
        (tail_update R r _ hr htail) hb hs
  | brk k =>
    simp only [execute, Option.some.injEq] at he
    subst next
    obtain ⟨t, ht, hs⟩ := runTo_sound none Q _ (check_break Q k hcheck)
      n _ (valid_none R spares hspares) binary hc
    refine ⟨t, ht, n + (64 + (if allOnes (stripPath false k Q) then 1 else 0) -
      (breakPath k Q).length), spares, hspares, ?_⟩
    exact target_frame n _ (breakPath k Q) (allOnes (stripPath false k Q)) 0 _
      R spares _ (by have := breakPath_length k Q; omega) htail
      (unchanged_rebase R spares) hs
  | cont k =>
    simp only [execute, Option.some.injEq] at he
    subst next
    obtain ⟨t, ht, hs⟩ := runTo_sound none Q _ (check_continue Q k hcheck)
      n _ (valid_none R spares hspares) binary hc
    refine ⟨t, ht, n + (64 - (continuePath k Q).length), spares, hspares, ?_⟩
    exact target_frame n _ (continuePath k Q) false 0 _ R spares _
      (by have := continuePath_length k Q; simp only [Bool.false_eq_true, if_false]; omega)
      htail (unchanged_rebase R spares) hs

theorem halt_frame (Q : List Bool) (R : Registers) (spares : List Nat)
    (n : Nat) (binary : Config 245) (hcheck : checkSite Q .halt = true)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary) :
    ∃ k : Nat, 0 < k ∧ (machineRouting245.runFrom binary k).state = none :=
  runHalt_sound Q (check_halt Q hcheck) n _ (valid_none R spares hspares).1 binary hc

end SetTheory.BusyBeaver.ZFC.InstructionRouting245
