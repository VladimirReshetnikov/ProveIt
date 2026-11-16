import PA195Simulation
import PA195GenericTrace
import PA195Control

/-! Standard-natural-number global simulation assembly. The machine-specific
validity/totality ingredients are explicit until supplied by the table audit. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195LocalQuotient

def projectConfig (c : Configuration) : Configuration :=
  ⟨project c.state, c.pos, c.tape⟩

def AtHalt (c : Configuration) : Prop := c.state = 254

theorem native_halt_maps (c : Configuration) (h : AtHalt c) : AtHalt (projectConfig c) := by
  change project c.state = 254
  rw [h]
  decide +kernel

theorem folded_halt_stuck (c : Configuration) (h : AtHalt c) : fullStep folded c = none := by
  have ht : ∀ b : Bool, lookup folded 254 b = none := by decide +kernel
  have hc : c.state = 254 := h
  simp [fullStep, hc, ht]

theorem run_eq_fullRun (rows : List Row) (n : Nat) (c : Configuration) :
    PA195GenericTrace.run (fullStep rows) n c = fullRun rows n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [PA195GenericTrace.run, fullRun]
    cases hs : fullStep rows c with
    | none => rfl
    | some d => simpa [hs] using ih d

theorem simulation_generic (c a : Configuration) (hh : History c)
    (hs : fullStep parent c = some a) :
    ∃ n, 0 < n ∧ PA195GenericTrace.run (fullStep folded) n (projectConfig c) =
      some (projectConfig a) := by
  obtain ⟨n, hn, hr⟩ := simulation_step c a hh hs
  refine ⟨n, hn, ?_⟩
  rw [run_eq_fullRun]
  exact hr

/-- Standard-natural-number trace equivalence from the stated table validity
and totality premises. These premises will be supplied by the exhaustive
parent-table certificate. -/
theorem halts_iff_of_control_facts
    (valid : Nat → Prop)
    (vstart : valid 74)
    (vstep : ∀ c a : Configuration, fullStep parent c = some a → valid a.state)
    (vtotal : ∀ c : Configuration, valid c.state → c.state ≠ 254 →
      ∃ a, fullStep parent c = some a)
    (p : Int) (t : Int → Bool) :
    PA195GenericTrace.Halts (fullStep parent) AtHalt ⟨74, p, t⟩ ↔
    PA195GenericTrace.Halts (fullStep folded) AtHalt ⟨project 74, p, t⟩ := by
  let inv : Configuration → Prop := fun c => History c ∧ valid c.state
  have hp : ∀ c a, inv c → fullStep parent c = some a → inv a := by
    intro c a _ hs
    exact ⟨history_step c a hs, vstep c a hs⟩
  have hs : ∀ c a, inv c → fullStep parent c = some a →
      ∃ k, 0 < k ∧ PA195GenericTrace.run (fullStep folded) k (projectConfig c) =
        some (projectConfig a) := by
    intro c a hi h
    exact simulation_generic c a hi.1 h
  have ht : ∀ c, inv c → ¬AtHalt c → ∃ a, fullStep parent c = some a := by
    intro c hi hn
    exact vtotal c hi.2 hn
  have hi : inv ⟨74, p, t⟩ := ⟨history_start t p, vstart⟩
  exact PA195GenericTrace.halts_iff (fullStep parent) (fullStep folded)
    projectConfig inv AtHalt AtHalt hp hs ht native_halt_maps folded_halt_stuck
    ⟨74, p, t⟩ hi

/-- The exact unfolded parent and folded 195-control native tables have the
same halting behavior on every tape and at every initial head position. -/
theorem halts_iff_any_tape (p : Int) (t : Int → Bool) :
    PA195GenericTrace.Halts (fullStep parent) AtHalt ⟨74, p, t⟩ ↔
    PA195GenericTrace.Halts (fullStep folded) AtHalt ⟨74, p, t⟩ := by
  have hs : validControl 74 := start_valid t p
  have h := halts_iff_of_control_facts validControl hs parent_step_valid parent_total p t
  have hp : project 74 = 74 := by decide +kernel
  simpa [hp] using h

#print axioms halts_iff_any_tape
#print axioms halts_iff_of_control_facts
#print axioms native_halt_maps
#print axioms folded_halt_stuck
#print axioms simulation_generic
end PA195LocalQuotient
