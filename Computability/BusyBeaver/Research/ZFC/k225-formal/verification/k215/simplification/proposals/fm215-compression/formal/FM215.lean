import FM215Data

namespace FM215

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- A finite Boolean certificate for every possible incoming row. -/
theorem incoming_rows : ∀ (q : State) (b : Bool),
    (old q b).all (fun a => decide
      ((a.2.2 = 124 → a.1 = true ∧ a.2.1 = true) ∧
       (a.2.2 = 127 → a.1 = false ∧ a.2.1 = true))) = true := by decide +kernel

/-- The only old entries to the merged states write their origin marker. -/
theorem incoming : ∀ (q : State) (b : Bool),
    match old q b with
    | none => True
    | some (w, right, z) =>
      (z = 124 → w = true ∧ right = true) ∧
      (z = 127 → w = false ∧ right = true) := by
  intro q b
  have hi := incoming_rows q b
  cases hr : old q b with
  | none => trivial
  | some a =>
    rw [hr] at hi
    exact of_decide_eq_true hi

/-- Outside the two merged roles, the exact rows differ only by phi. -/
theorem outer : ∀ (q : State) (b : Bool), q ≠ 124 → q ≠ 127 →
    new q b = (old q b).map mapAction := by decide +kernel

theorem inv_advance {c : Config} {a : Action}
    (hr : old c.q (c.tape c.head) = some a) : Inv (advance c a) := by
  obtain ⟨w, right, z⟩ := a
  have hi := incoming c.q (c.tape c.head)
  rw [hr] at hi
  rcases hi with ⟨h124, h127⟩
  constructor
  · intro hz
    obtain ⟨hw, hd⟩ := h124 hz
    simp [advance, hw, hd, put]
  · intro hz
    obtain ⟨hw, hd⟩ := h127 hz
    simp [advance, hw, hd, put]

theorem inv_step {c c' : Config} (hs : step old c = some c') : Inv c' := by
  unfold step at hs
  cases hr : old c.q (c.tape c.head) with
  | none => rw [hr] at hs; cases hs
  | some a =>
    rw [hr] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst c'
    exact inv_advance hr

/-- The three-step replacement preserves every tape cell. -/
theorem zero_block (h : Int) (t : Tape) (hc : t h = false) :
    PositiveSimulation.run (step new) 3 ⟨124, h, t⟩ =
      some ⟨if t (h - 1) then 62 else 14, h + 1, t⟩ := by
  have first : step new ⟨124, h, t⟩ = some ⟨127, h - 1, t⟩ := by
    simpa [Int.sub_eq_add_neg] using step_same (c := ⟨124, h, t⟩) hc
      (show new 124 false = some (false, false, 127) from rfl)
  cases hm : t (h - 1) with
  | false =>
    have second : step new ⟨127, h - 1, t⟩ = some ⟨8, h, t⟩ := by
      simpa using step_same (c := ⟨127, h - 1, t⟩) hm
        (show new 127 false = some (false, true, 8) from rfl)
    have third := step_same (c := ⟨8, h, t⟩) hc
      (show new 8 false = some (false, true, 14) from rfl)
    simp [PositiveSimulation.run, first, second, third]
  | true =>
    have second : step new ⟨127, h - 1, t⟩ = some ⟨109, h, t⟩ := by
      simpa using step_same (c := ⟨127, h - 1, t⟩) hm
        (show new 127 true = some (true, true, 109) from rfl)
    have third := step_same (c := ⟨109, h, t⟩) hc
      (show new 109 false = some (false, true, 62) from rfl)
    simp [PositiveSimulation.run, first, second, third]

theorem lift_advance (c : Config) (a : Action) :
    lift (advance c a) = advance (lift c) (mapAction a) := rfl

theorem outer_step {c c' : Config} (h124 : c.q ≠ 124) (h127 : c.q ≠ 127)
    (hs : step old c = some c') : step new (lift c) = some (lift c') := by
  have hp : phi c.q = c.q := by simp [phi, h127]
  unfold step at hs ⊢
  simp only [lift, hp, outer c.q (c.tape c.head) h124 h127]
  cases hr : old c.q (c.tape c.head) with
  | none => rw [hr] at hs; cases hs
  | some a =>
    rw [hr] at hs
    simp only [Option.map_some, Option.some.injEq] at hs ⊢
    subst c'
    simpa only [lift, hp] using (lift_advance c a).symm

theorem sim_step {c c' : Config} (hc : Inv c) (hs : step old c = some c') :
    PositiveSimulation.Reach1 (step new) (lift c) (lift c') := by
  by_cases h124 : c.q = 124
  · cases hb : c.tape c.head with
    | false =>
      have hm := hc.1 h124
      have ho := step_same (M := old) (c := c) hb
        (by simpa [h124] using (show old 124 false = some (false, true, 62) from rfl))
      rw [ho] at hs
      cases hs
      refine ⟨2, ?_⟩
      simpa [lift, h124, phi, hm] using zero_block c.head c.tape hb
    | true =>
      have ho := step_same (M := old) (c := c) hb
        (by simpa [h124] using (show old 124 true = some (true, true, 138) from rfl))
      rw [ho] at hs
      cases hs
      have hn := step_same (M := new) (c := lift c) hb
        (by simpa [lift, h124, phi] using (show new 124 true = some (true, true, 138) from rfl))
      exact ⟨0, by simpa [lift, phi] using hn⟩
  · by_cases h127 : c.q = 127
    · cases hb : c.tape c.head with
      | false =>
        have hm := hc.2 h127
        have ho := step_same (M := old) (c := c) hb
          (by simpa [h127] using (show old 127 false = some (false, true, 14) from rfl))
        rw [ho] at hs
        cases hs
        refine ⟨2, ?_⟩
        simpa [lift, h127, phi, hm] using zero_block c.head c.tape hb
      | true =>
        have ho := step_same (M := old) (c := c) hb
          (by simpa [h127] using (show old 127 true = some (true, true, 138) from rfl))
        rw [ho] at hs
        cases hs
        have hn := step_same (M := new) (c := lift c) hb
          (by simpa [lift, h127, phi] using (show new 124 true = some (true, true, 138) from rfl))
        exact ⟨0, by simpa [lift, phi] using hn⟩
    · exact ⟨0, by simpa using outer_step h124 h127 hs⟩

theorem sim_stop {c : Config} (hs : step old c = none) :
    PositiveSimulation.Halts (step new) (lift c) := by
  have h124 : c.q ≠ 124 := by
    intro he
    cases hb : c.tape c.head <;> (simp only [step, he, hb] at hs; cases hs)
  have h127 : c.q ≠ 127 := by
    intro he
    cases hb : c.tape c.head <;> (simp only [step, he, hb] at hs; cases hs)
  refine ⟨0, lift c, rfl, ?_⟩
  unfold step at hs ⊢
  simp only [lift, phi, h127, if_false, outer c.q (c.tape c.head) h124 h127]
  cases hr : old c.q (c.tape c.head) with
  | none => rfl
  | some a => rw [hr] at hs; cases hs

/-- All initial tapes and head positions are covered from the designated state 0. -/
theorem all_tapes_halts_iff (h : Int) (t : Tape) :
    PositiveSimulation.Halts (step old) ⟨0, h, t⟩ ↔
    PositiveSimulation.Halts (step new) ⟨0, h, t⟩ := by
  apply PositiveSimulation.halts_iff (R := fun c d => Inv c ∧ d = lift c)
  · intro c c' d hc hs
    obtain ⟨hi, rfl⟩ := hc
    exact ⟨lift c', ⟨inv_step hs, rfl⟩, sim_step hi hs⟩
  · intro c d hc hs
    obtain ⟨_, rfl⟩ := hc
    exact sim_stop hs
  · exact ⟨by simp [Inv], by simp [lift, phi]⟩

theorem blank_halts_iff :
    PositiveSimulation.Halts (step old) ⟨0, 0, fun _ => false⟩ ↔
    PositiveSimulation.Halts (step new) ⟨0, 0, fun _ => false⟩ :=
  all_tapes_halts_iff 0 (fun _ => false)

#print axioms all_tapes_halts_iff
#print axioms blank_halts_iff

end FM215
