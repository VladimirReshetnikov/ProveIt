/- UNCOMPILED research draft. Adapted from the attributed ProveIt
proposals/k215-transport/formal/PositiveStutter.lean at
beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc. Original proof code is inherited.
The change weakens terminal agreement to eventual terminal halting; it
does not claim a new mathematical discovery or a new compiled endpoint. -/
import Init

/-!
Positive block simulation for deterministic partial transition systems.

This file is independent of the ProveIt development.  A terminal configuration
has no successor.  A successful finite run contains no earlier terminal
configuration.  One positive block simulation, plus terminal halting preservation at
related configurations, suffices for equivalence of finite halting.

The positivity hypothesis is essential to the reverse implication: it lets
the proof consume a strictly positive part of a terminating target run.
-/

namespace TerminalDrain

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
    {n : Nat} {c d : C} (h : run next n c = some d) (hd : Halts next d) :
    Halts next c := by
  obtain ⟨m, e, hm, he⟩ := hd
  refine ⟨n + m, e, ?_, he⟩
  rw [run_add, h]
  exact hm

theorem halt_now {C : Type u} {next : C → Option C} {c : C}
    (h : next c = none) : Halts next c :=
  ⟨0, c, rfl, h⟩

/-- A successful prefix cannot run beyond a terminal endpoint. -/
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

/-- A source transition is implemented by a nonempty target block. -/
structure Simulation {A : Type u} {B : Type v}
    (stepA : A → Option A) (stepB : B → Option B)
    (R : A → B → Prop) : Prop where
  terminal : ∀ {a b}, R a b → stepA a = none → Halts stepB b
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
    exact hS.terminal hab hd
  | succ n ih =>
    cases he : stepA a with
    | none =>
      simp only [run, he, Option.bind_none] at hn
      contradiction
    | some a' =>
      simp only [run, he, Option.bind_some] at hn
      obtain ⟨k, b', _, hk, hab'⟩ := hS.advance hab he
      exact halts_of_run hk (ih hab' hn)

theorem Simulation.reflects_halts (hS : Simulation stepA stepB R)
    {a b} (hab : R a b) (hb : Halts stepB b) : Halts stepA a := by
  obtain ⟨n, d, hn, hd⟩ := hb
  induction n using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    cases he : stepA a with
    | none => exact halt_now he
    | some a' =>
      obtain ⟨k, b', hkpos, hk, hab'⟩ := hS.advance hab he
      obtain ⟨m, hnm, hm⟩ := terminal_suffix k hn hd hk
      have hmn : m < n := by omega
      have ha' : Halts stepA a' := ih m hmn hab' hm
      exact halts_of_run (n := 1) (by simp only [run, he, Option.bind_some]) ha'

/-- One positive simulation proves halting equivalence; no reverse certificate
or fairness assumption is required. -/
theorem Simulation.halts_iff (hS : Simulation stepA stepB R)
    {a b} (hab : R a b) : Halts stepA a ↔ Halts stepB b :=
  ⟨hS.preserves_halts hab, hS.reflects_halts hab⟩

theorem Simulation.nonhalting_iff (hS : Simulation stepA stepB R)
    {a b} (hab : R a b) : (¬ Halts stepA a) ↔ (¬ Halts stepB b) :=
  not_congr (hS.halts_iff hab)

#print axioms Simulation.halts_iff
#print axioms Simulation.nonhalting_iff

end TerminalDrain
