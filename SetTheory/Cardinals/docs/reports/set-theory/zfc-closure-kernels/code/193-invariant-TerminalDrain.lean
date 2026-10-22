import Init

/-!
Positive simulation with a finite terminal drain.

Adapted from the checked PositiveStutter proposal in ProveIt's
`k215-transport/formal/PositiveStutter.lean` (snapshot 57541fe0cfe3).
The immediate terminal-agreement field is replaced by `finish`: the source
may stop before the target completes its finite epilogue. Reflection uses
only `advance`, and in particular needs no reverse simulation.
-/

namespace SetTheory.BusyBeaver.ZFC.TerminalDrain

universe u v

def run {C : Type u} (next : C → Option C) : Nat → C → Option C
  | 0, c => some c
  | n + 1, c => (next c).bind (run next n)

def Halts {C : Type u} (next : C → Option C) (c : C) : Prop :=
  ∃ n d, run next n c = some d ∧ next d = none

theorem run_add {C : Type u} (next : C → Option C) (n m : Nat) (c : C) :
    run next (n + m) c = (run next n c).bind (run next m) := by
  induction n generalizing c with
  | zero => simp only [Nat.zero_add, run, Option.bind_some]
  | succ n ih =>
      simp only [Nat.succ_add, run]
      cases hc : next c with
      | none => rfl
      | some c' => exact ih c'

theorem halts_of_run {C : Type u} {next : C → Option C}
    {n : Nat} {c d : C} (h : run next n c = some d) (hd : Halts next d) : Halts next c := by
  obtain ⟨m, e, hm, he⟩ := hd
  exact ⟨n + m, e, by rw [run_add, h]; exact hm, he⟩

theorem halt_now {C : Type u} {next : C → Option C} {c : C}
    (h : next c = none) : Halts next c := ⟨0, c, rfl, h⟩

/-- A successful prefix cannot pass a terminal endpoint. -/
theorem terminal_suffix {C : Type u} {next : C → Option C}
    (k : Nat) {n : Nat} {c c' d : C}
    (hwhole : run next n c = some d) (hd : next d = none)
    (hprefix : run next k c = some c') :
    ∃ m, n = k + m ∧ run next m c' = some d := by
  induction k generalizing n c with
  | zero =>
      simp only [run, Option.some.injEq] at hprefix
      subst c'
      exact ⟨n, by omega, hwhole⟩
  | succ k ih =>
      cases n with
      | zero =>
          simp only [run, Option.some.injEq] at hwhole
          subst d
          simp only [run, hd, Option.bind_none] at hprefix
          contradiction
      | succ n =>
          cases hc : next c with
          | none =>
              simp only [run, hc, Option.bind_none] at hwhole
              contradiction
          | some c1 =>
              simp only [run, hc, Option.bind_some] at hwhole hprefix
              obtain ⟨m, hm, hr⟩ := ih hwhole hprefix
              exact ⟨m, by omega, hr⟩

theorem halts_iff_of_run {C : Type u} {next : C → Option C}
    {n : Nat} {c d : C} (h : run next n c = some d) : Halts next c ↔ Halts next d := by
  constructor
  · rintro ⟨m, e, hm, he⟩
    obtain ⟨k, _, hk⟩ := terminal_suffix n hm he h
    exact ⟨k, e, hk, he⟩
  · exact halts_of_run h

/-- Every source step consumes a positive target run. A source terminal
configuration may require a finite target epilogue. -/
structure Simulation {A : Type u} {B : Type v}
    (stepA : A → Option A) (stepB : B → Option B) (R : A → B → Prop) : Prop where
  finish : ∀ {a b}, R a b → stepA a = none → Halts stepB b
  advance : ∀ {a b a'}, R a b → stepA a = some a' →
    ∃ k b', 0 < k ∧ run stepB k b = some b' ∧ R a' b'

variable {A : Type u} {B : Type v}
variable {stepA : A → Option A} {stepB : B → Option B} {R : A → B → Prop}

theorem Simulation.preserves_halts (hS : Simulation stepA stepB R)
    {a b} (hab : R a b) (ha : Halts stepA a) : Halts stepB b := by
  obtain ⟨n, d, hn, hd⟩ := ha
  induction n generalizing a b with
  | zero =>
      simp only [run, Option.some.injEq] at hn
      subst d
      exact hS.finish hab hd
  | succ n ih =>
      cases he : stepA a with
      | none =>
          simp only [run, he, Option.bind_none] at hn
          contradiction
      | some a' =>
          simp only [run, he, Option.bind_some] at hn
          obtain ⟨k, b', _, hk, hab'⟩ := hS.advance hab he
          exact halts_of_run hk (ih hab' hn)

/-- Positivity alone suffices to reflect termination. `finish` is not used. -/
theorem reflects_halts
    (advance : ∀ {a b a'}, R a b → stepA a = some a' →
      ∃ k b', 0 < k ∧ run stepB k b = some b' ∧ R a' b')
    {a b} (hab : R a b) (hb : Halts stepB b) : Halts stepA a := by
  obtain ⟨n, d, hn, hd⟩ := hb
  induction n using Nat.strongRecOn generalizing a b with
  | ind n ih =>
      cases he : stepA a with
      | none => exact halt_now he
      | some a' =>
          obtain ⟨k, b', hkpos, hk, hab'⟩ := advance hab he
          obtain ⟨m, hnm, hm⟩ := terminal_suffix k hn hd hk
          have ha' : Halts stepA a' := ih m (by omega) hab' hm
          exact halts_of_run (n := 1) (by simp only [run, he, Option.bind_some]) ha'

theorem Simulation.halts_iff (hS : Simulation stepA stepB R)
    {a b} (hab : R a b) : Halts stepA a ↔ Halts stepB b :=
  ⟨hS.preserves_halts hab, reflects_halts hS.advance hab⟩

/-- Partialize a deterministic time counter at the first accepted time. -/
def counter (done : Nat → Prop) [DecidablePred done] (n : Nat) : Option Nat :=
  if done n then none else some (n + 1)

theorem counter_halts_of_later (done : Nat → Prop) [DecidablePred done]
    (k n : Nat) (h : done (n + k)) : Halts (counter done) n := by
  induction k generalizing n with
  | zero =>
      simp only [Nat.add_zero] at h
      exact halt_now (by simp [counter, h])
  | succ k ih =>
      by_cases hn : done n
      · exact halt_now (by simp [counter, hn])
      · apply halts_of_run (n := 1) (d := n + 1)
        · simp [run, counter, hn]
        · exact ih (n + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)

/-- Halting of the counter is exactly existence of an accepted time. -/
theorem counter_halts_iff (done : Nat → Prop) [DecidablePred done] :
    Halts (counter done) 0 ↔ ∃ n, done n := by
  constructor
  · rintro ⟨_, n, _, hn⟩
    exact ⟨n, by simpa [counter] using hn⟩
  · rintro ⟨n, hn⟩
    exact counter_halts_of_later done n 0 (by simpa using hn)

#print axioms Simulation.halts_iff
#print axioms counter_halts_iff

end SetTheory.BusyBeaver.ZFC.TerminalDrain
