import Init

/-!
Positive finite stuttering transfers halting in both directions.

This file is independent of ProveIt's machine implementation. A client supplies
an invariant on the source configurations, a (possibly noninjective) map to
configurations of a deterministic target, and positive target blocks simulating
source steps. Only preservation of source terminal configurations is required:
no target invariant, reverse simulation, injectivity, or uniform block bound.
-/

namespace PositiveStuttering

universe u v

/-- Exactly `n` successful transitions; the terminal state is not executed. -/
inductive Steps {C : Type u} (step : C → Option C) : Nat → C → C → Prop where
  | refl (c : C) : Steps step 0 c c
  | next {n : Nat} {c c' d : C} :
      step c = some c' → Steps step n c' d → Steps step (n + 1) c d

/-- A finite run reaches a configuration at which no transition is defined. -/
def Halts {C : Type u} (step : C → Option C) (c : C) : Prop :=
  ∃ n d, Steps step n c d ∧ step d = none

namespace Steps

variable {C : Type u} {step : C → Option C}

theorem append {n m : Nat} {a b c : C}
    (h₁ : Steps step n a b) (h₂ : Steps step m b c) :
    Steps step (n + m) a c := by
  induction h₁ generalizing m c with
  | refl => simpa using h₂
  | next h ht ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.next h (ih h₂)

/-- A successful prefix of a halting run cannot extend past its terminal state.
Determinism identifies the intermediate configurations. -/
theorem prefix_halt {m : Nat} {a b : C} (hp : Steps step m a b) :
    ∀ {n : Nat} {z : C}, Steps step n a z → step z = none →
      m ≤ n ∧ Steps step (n - m) b z := by
  induction hp with
  | refl =>
      intro n z hn hz
      exact ⟨Nat.zero_le n, hn⟩
  | @next m a a' b hs ht ih =>
      intro n z hn hz
      cases hn with
      | refl =>
          rw [hz] at hs
          cases hs
      | @next n _ a'' _ hs' hn' =>
          have heq : a' = a'' := Option.some.inj (hs.symm.trans hs')
          subst a''
          obtain ⟨hle, htail⟩ := ih hn' hz
          exact ⟨Nat.succ_le_succ hle, by rw [Nat.succ_sub_succ_eq_sub]; exact htail⟩

end Steps

/-- The complete client interface for halting-equivalence transport. -/
structure Simulation {A : Type u} {B : Type v}
    (old : A → Option A) (new : B → Option B)
    (map : A → B) (Inv : A → Prop) : Prop where
  preserve : ∀ c c', Inv c → old c = some c' → Inv c'
  terminal : ∀ c, Inv c → old c = none → new (map c) = none
  block : ∀ c c', Inv c → old c = some c' →
    ∃ m, 0 < m ∧ Steps new m (map c) (map c')

namespace Simulation

variable {A : Type u} {B : Type v}
variable {old : A → Option A} {new : B → Option B}
variable {map : A → B} {Inv : A → Prop}

/-- Map any source run to a target run, retaining the source invariant. -/
theorem map_steps (sim : Simulation old new map Inv)
    {n : Nat} {a b : A} (h : Steps old n a b) (ha : Inv a) :
    ∃ m, Steps new m (map a) (map b) ∧ Inv b := by
  induction h with
  | refl => exact ⟨0, Steps.refl _, ha⟩
  | next hs ht ih =>
      have hb := sim.preserve _ _ ha hs
      obtain ⟨m, hm, hblock⟩ := sim.block _ _ ha hs
      obtain ⟨k, hk, hend⟩ := ih hb
      exact ⟨m + k, hblock.append hk, hend⟩

theorem halts_forward (sim : Simulation old new map Inv)
    {c : A} (hc : Inv c) : Halts old c → Halts new (map c) := by
  rintro ⟨n, d, hrun, hstop⟩
  obtain ⟨m, hmap, hd⟩ := sim.map_steps hrun hc
  exact ⟨m, map d, hmap, sim.terminal d hd hstop⟩

/-- Positivity is used here: every simulated source step strictly decreases the
remaining length of a halting target run. -/
theorem halts_backward (sim : Simulation old new map Inv)
    {c : A} (hc : Inv c) : Halts new (map c) → Halts old c := by
  have go : ∀ n : Nat, ∀ a : A, Inv a →
      (∃ z, Steps new n (map a) z ∧ new z = none) → Halts old a := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro a ha hhalt
        obtain ⟨z, hrun, hstop⟩ := hhalt
        cases hs : old a with
        | none => exact ⟨0, a, Steps.refl _, hs⟩
        | some a' =>
            obtain ⟨m, hm, hblock⟩ := sim.block a a' ha hs
            obtain ⟨hmn, htail⟩ := hblock.prefix_halt hrun hstop
            have hlt : n - m < n := Nat.sub_lt (Nat.lt_of_lt_of_le hm hmn) hm
            obtain ⟨k, w, hk, hw⟩ :=
              ih (n - m) hlt a' (sim.preserve a a' ha hs) ⟨z, htail, hstop⟩
            exact ⟨k + 1, w, Steps.next hs hk, hw⟩
  rintro ⟨n, z, hrun, hstop⟩
  exact go n c hc ⟨z, hrun, hstop⟩

/-- A forward positive stuttering simulation of deterministic partial functions
preserves and reflects halting on the source invariant. -/
theorem halts_iff (sim : Simulation old new map Inv)
    {c : A} (hc : Inv c) : Halts old c ↔ Halts new (map c) :=
  ⟨sim.halts_forward hc, sim.halts_backward hc⟩

end Simulation

#print axioms Simulation.halts_iff

end PositiveStuttering
