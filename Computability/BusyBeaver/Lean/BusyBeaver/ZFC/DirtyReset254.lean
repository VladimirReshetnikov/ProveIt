import BusyBeaver.ZFC.EnumStackCount254

/-!
Six arbitrary-data reset starts for the actual Enum254 enumerator.
Attributed to intake156/source49, “Reset synchronization and HOD calibration”,
source snapshot fab89c5d26b81cd2ccab2ee5d213ff23725c7726. The report proves the
ordinary six-counter theorem and distinguishes an initial AX's eight good
schema rows from the ten rows available after the active formulas are good.
The marked-occurrence barrier is inherited from intake155/source42 through
EnumStackCount254. The original enumerator's Mira-Cult, Jeff Ketchersid and
Andrew James Wade attribution is retained by its imported source lineage.

We use the unconditional eight-row shield at candidate6 directly. All earlier
commands needed here are total, except candidate3's NIP; a preceding MP makes
its cache0. Thus no assumption about any of the four working fields is needed
at counters0,1,2,4,5,6. These are actual six-register scheduler theorems, not a
new binary initialization or arithmetic proof-code formalization.
-/

namespace SetTheory.BusyBeaver.ZFC.DirtyReset254

open Code254 Enum254 EnumStackBarrier254 EnumStackCount254

attribute [local irreducible] Code254.P

/-- A clean candidate boundary, retaining all four working fields literally. -/
def boundary (k : Nat) (w : W) : St := ⟨0, k, w.tw, w.ws, w.d, w.h⟩

private theorem commands_enc (c : Cmd) (cs : List Cmd) :
    commands (encL c cs) = c :: cs := by
  simp only [commands, decode_encL]

theorem commands_zero : commands 0 = [.mp 0] := by
  simp only [commands, decode_zero]

theorem commands_one : commands 1 = [.drop 0] := by
  have hc : encL (.drop 0) [] = 1 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  simpa only [hc] using commands_enc (.drop 0) []

theorem commands_two : commands 2 = [.mp 1] := by
  have hc : encL (.mp 1) [] = 2 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  simpa only [hc] using commands_enc (.mp 1) []

theorem commands_three : commands 3 = [.nip 0] := by
  have hc : encL (.nip 0) [] = 3 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  simpa only [hc] using commands_enc (.nip 0) []

theorem commands_four : commands 4 = [.drop 1] := by
  have hc : encL (.drop 1) [] = 4 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  simpa only [hc] using commands_enc (.drop 1) []

theorem commands_five : commands 5 = [.mp 0, .mp 0] := by
  have hc : encL (.mp 0) [.mp 0] = 5 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  simpa only [hc] using commands_enc (.mp 0) [.mp 0]

theorem commands_six : commands 6 = [.ax 0 0 0 0] := by
  have hc : encL (.ax 0 0 0 0) [] = 6 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  simpa only [hc] using commands_enc (.ax 0 0 0 0) []

/-- Exact earlier-candidate balance, not a supplied numerical hypothesis. -/
theorem credit_seven : credit 7 = 1 := by
  rw [credit_succ 6, credit_succ 5, credit_succ 4, credit_succ 3,
    credit_succ 2, credit_succ 1, credit_one]
  simp only [commands_one, commands_two, commands_three, commands_four,
    commands_five, commands_six, count_cons, count_nil, isDrop, isNip]
  rfl

private theorem halts_step_iff {s out : St} (he : enumStep s = some out) :
    EnumSafeStart254.HaltsFrom s ↔ EnumSafeStart254.HaltsFrom out := by
  constructor
  · rintro ⟨n, st, hr, hh⟩
    cases n with
    | zero =>
        have hst : s = st := Option.some.inj hr
        subst st
        rw [he] at hh
        cases hh
    | succ n => exact ⟨n, st, by simpa only [run, he] using hr, hh⟩
  · exact EnumSafeStart254.halts_from_run 1 (by simp only [run, he])

/-- A proved active finite prefix cannot contain an earlier halt. -/
theorem halts_run_iff (n : Nat) (s out : St) (hr : run n s = some out) :
    EnumSafeStart254.HaltsFrom s ↔ EnumSafeStart254.HaltsFrom out := by
  induction n generalizing s with
  | zero => cases hr; exact Iff.rfl
  | succ n ih =>
      cases he : enumStep s with
      | none => simp only [run, he] at hr; cases hr
      | some s1 =>
          have hrest : run n s1 = some out := by simpa only [run, he] using hr
          exact (halts_step_iff he).trans (ih s1 hrest)

private theorem single_run {k : Nat} {c : Cmd} {w out : W}
    (hc : commands k = [c]) (he : cstep c w = some out) :
    run 1 (boundary k w) = some (boundary (k + 1) out) := by
  have hx : cexec (commands k) (toW (boundary k w)) = some out := by
    have hw : toW (boundary k w) = w := by cases w; rfl
    rw [hc, hw]
    simp only [cexec, he]
  have hr := candidate_some k (boundary k w) out rfl rfl hx
  simpa only [hc, List.length_cons, List.length_nil, boundary] using hr

private theorem mp_total (x : Nat) (w : W) :
    ∃ out, cstep (.mp x) w = some out ∧ out.h = 0 := by
  obtain ⟨t, stack, d, h⟩ := w
  by_cases hm : wim t (d + x) = h
  · exact ⟨⟨d + x, P 0 stack, d + x, 0⟩, by simp only [cstep, hm, if_true], rfl⟩
  · exact ⟨⟨0, stack, d + x, 0⟩, by simp only [cstep, hm, if_false], rfl⟩

private theorem drop_total (x : Nat) (w : W) : ∃ out, cstep (.drop x) w = some out :=
  ⟨⟨w.h, P w.tw w.ws, w.d + x, w.h⟩, rfl⟩

private theorem nip_zero_cache (w : W) (hh : w.h = 0) :
    ∃ out, cstep (.nip 0) w = some out := by
  refine ⟨⟨w.tw, (unP w.ws).2, w.d, (unP w.ws).1⟩, ?_⟩
  simp only [cstep, hh, Nat.zero_ne_one, if_false, Nat.add_zero]

/-- An entirely dirty AX still puts eight unconditional logical axioms above
an exact arbitrary tail containing its old generalized cache and old top. -/
theorem ax_eight_prefix (t stack d h : Nat) :
    SafeStack (P (wal d h) (P t stack)) 8 (axStack d h h 0 0 t stack) := by
  exact safeStack_cons (C254.r1 d h) <|
    safeStack_cons (C254.r2 d h 0) <|
    safeStack_cons (C254.r3 d h 0) <|
    safeStack_cons (C254.r4 d h 0) <|
    safeStack_cons (C254.r5 d h 0) <|
    safeStack_cons (C254.r6 d h) <|
    safeStack_cons (C254.r7 d h 0) <|
    safeStack_cons (C254.r8 d h 0 0) <| safeStack_nil _

/-- Candidate6 immediately supplies the shield, whatever all four working
fields contain. Its exact output has pl0, np7, d0 and cache0. -/
theorem six_start_iff (w : W) :
    EnumSafeStart254.HaltsFrom (boundary 6 w) ↔ C254 F := by
  let out : W := ⟨gate w.d w.h 0, axStack w.d w.h w.h 0 0 w.tw w.ws, 0, 0⟩
  have he : cstep (.ax 0 0 0 0) w = some out := by
    simp only [cstep, Nat.add_zero, out]
  have hr := single_run commands_six he
  apply (halts_run_iff 1 (boundary 6 w) (boundary 7 out) hr).trans
  apply credit_start_iff 7 (P (wal w.d w.h) (P w.tw w.ws)) (boundary 7 out) rfl rfl
  rw [credit_seven]
  exact ⟨gate_good _ _ _, C254.truth,
    safeStack_weaken (by omega) (ax_eight_prefix _ _ _ _)⟩

theorem five_start_iff (w : W) :
    EnumSafeStart254.HaltsFrom (boundary 5 w) ↔ C254 F := by
  obtain ⟨w1, h1, _⟩ := mp_total 0 w
  obtain ⟨w2, h2, _⟩ := mp_total 0 w1
  have hx : cexec (commands 5) (toW (boundary 5 w)) = some w2 := by
    rw [commands_five]
    simp only [cexec, toW, boundary, h1, h2]
  have hr := candidate_some 5 (boundary 5 w) w2 rfl rfl hx
  have hr2 : run 2 (boundary 5 w) = some (boundary 6 w2) := by
    simpa only [commands_five, List.length_cons, List.length_nil, boundary] using hr
  exact (halts_run_iff 2 _ _ hr2).trans (six_start_iff w2)

theorem four_start_iff (w : W) :
    EnumSafeStart254.HaltsFrom (boundary 4 w) ↔ C254 F := by
  obtain ⟨out, he⟩ := drop_total 1 w
  exact (halts_run_iff 1 _ _ (single_run commands_four he)).trans (five_start_iff out)

theorem three_zero_cache_iff (w : W) (hh : w.h = 0) :
    EnumSafeStart254.HaltsFrom (boundary 3 w) ↔ C254 F := by
  obtain ⟨out, he⟩ := nip_zero_cache w hh
  exact (halts_run_iff 1 _ _ (single_run commands_three he)).trans (four_start_iff out)

theorem two_start_iff (w : W) :
    EnumSafeStart254.HaltsFrom (boundary 2 w) ↔ C254 F := by
  obtain ⟨out, he, hh⟩ := mp_total 1 w
  exact (halts_run_iff 1 _ _ (single_run commands_two he)).trans (three_zero_cache_iff out hh)

theorem one_start_iff (w : W) :
    EnumSafeStart254.HaltsFrom (boundary 1 w) ↔ C254 F := by
  obtain ⟨out, he⟩ := drop_total 0 w
  exact (halts_run_iff 1 _ _ (single_run commands_one he)).trans (two_start_iff out)

theorem zero_start_iff (w : W) :
    EnumSafeStart254.HaltsFrom (boundary 0 w) ↔ C254 F := by
  obtain ⟨out, he, _⟩ := mp_total 0 w
  exact (halts_run_iff 1 _ _ (single_run commands_zero he)).trans (one_start_iff out)

/-- All four working fields, including d and the entire dirty stack, are
unrestricted. No supplied credit or semantic-invariant premise is retained. -/
theorem six_dirty_starts_iff (n t stack d h : Nat)
    (hn : n ∈ [0, 1, 2, 4, 5, 6]) :
    EnumSafeStart254.HaltsFrom ⟨0, n, t, stack, d, h⟩ ↔ C254 F := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact zero_start_iff ⟨t, stack, d, h⟩
  · exact one_start_iff ⟨t, stack, d, h⟩
  · exact two_start_iff ⟨t, stack, d, h⟩
  · exact four_start_iff ⟨t, stack, d, h⟩
  · exact five_start_iff ⟨t, stack, d, h⟩
  · exact six_start_iff ⟨t, stack, d, h⟩

/-- The excluded counter has a literal immediate halt at cache1. The
conditional consistency counterexample requires no inference about bad pops. -/
theorem three_cache_one_halts (t stack d : Nat) :
    EnumSafeStart254.HaltsFrom ⟨0, 3, t, stack, d, 1⟩ := by
  refine ⟨0, _, rfl, ?_⟩
  have hc : encL (.nip 0) [] = 3 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  change execAt 3 4 ⟨0, 3, t, stack, d, 1⟩ = none
  rw [← hc, encL, execAt_pack]
  simp only [toW, cstep, if_true]

end SetTheory.BusyBeaver.ZFC.DirtyReset254
