import BusyBeaver.ZFC.TableRouting245

/-!
The local predecessor invariant needed by the compensated 244-state fold.
This module concerns only the already checked original Routing245 table.
It quantifies over every Core configuration (arbitrary finite-support tape),
and every natural duration, with no register-frame or runtime hypothesis.
The source is a draft until separately checked by the root proof runner.
-/
namespace SetTheory.BusyBeaver.ZFC.Routing245Invariant

/-- The old68 and old167 entries have a one immediately to their left.
At old81 a left one entails a second one two cells to the left. -/
def Holds (c : Config 245) : Prop :=
  (c.state = some (oldStateRouting245 68) →
    Tape.read c.tape (c.head - 1) = true) ∧
  (c.state = some (oldStateRouting245 81) →
    Tape.read c.tape (c.head - 1) = true →
      Tape.read c.tape (c.head - 2) = true) ∧
  (c.state = some (oldStateRouting245 167) →
    Tape.read c.tape (c.head - 1) = true)

/-- Both incoming rows write one and move right. -/
private theorem into68_action : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 68) →
      machineRouting245.transition q b =
        ⟨true, .right, some (oldStateRouting245 68)⟩ := by
  decide +kernel

/-- Both incoming rows write one and move right. -/
private theorem into167_action : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 167) →
      machineRouting245.transition q b =
        ⟨true, .right, some (oldStateRouting245 167)⟩ := by
  decide +kernel

private theorem into81_cases : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 81) →
      (q = oldStateRouting245 68 ∧ b = true) ∨
      (q = oldStateRouting245 123 ∧ b = false) := by
  decide +kernel

private theorem row68_true :
    machineRouting245.transition (oldStateRouting245 68) true =
      ⟨true, .right, some (oldStateRouting245 81)⟩ := by decide +kernel

private theorem row123_false :
    machineRouting245.transition (oldStateRouting245 123) false =
      ⟨false, .right, some (oldStateRouting245 81)⟩ := by decide +kernel

private theorem start_distinct :
    oldStateRouting245 95 ≠ oldStateRouting245 68 ∧
      oldStateRouting245 95 ≠ oldStateRouting245 81 ∧
      oldStateRouting245 95 ≠ oldStateRouting245 167 := by decide +kernel

/-- The invariant is vacuous at the shared start for arbitrary head and tape. -/
theorem start_holds (head : Int) (tape : Tape) :
    Holds ⟨some (oldStateRouting245 95), head, tape⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    exact False.elim (start_distinct.1 (Option.some.inj hs))
  · intro hs
    exact False.elim (start_distinct.2.1 (Option.some.inj hs))
  · intro hs
    exact False.elim (start_distinct.2.2 (Option.some.inj hs))

/-- Literal canonical state zero, head zero and the all-zero tape. -/
theorem initial_holds : Holds (initial 245) := by
  change Holds ⟨some (oldStateRouting245 95), 0, []⟩
  exact start_holds 0 []

/-- The finite incoming-row facts preserve the invariant in one literal step.
Already halted configurations are stationary and are included. -/
theorem step_holds (c : Config 245) (hc : Holds c) :
    Holds (machineRouting245.step c) := by
  rcases c with ⟨state, head, tape⟩
  cases state with
  | none => exact hc
  | some q =>
    refine ⟨?_, ?_, ?_⟩
    · intro hn
      change (machineRouting245.transition q (Tape.read tape head)).next =
        some (oldStateRouting245 68) at hn
      have ha := into68_action q (Tape.read tape head) hn
      change Tape.read
        (Tape.write tape head (machineRouting245.transition q (Tape.read tape head)).write)
        ((machineRouting245.transition q (Tape.read tape head)).move.apply head - 1) = true
      rw [ha]
      change Tape.read (Tape.write tape head true) (head + 1 - 1) = true
      rw [show head + 1 - 1 = head by omega]
      exact Tape.read_write_same tape head true
    · intro hn hleft
      change (machineRouting245.transition q (Tape.read tape head)).next =
        some (oldStateRouting245 81) at hn
      rcases into81_cases q (Tape.read tape head) hn with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · have hprior : Tape.read tape (head - 1) = true := hc.1 rfl
        change Tape.read
          (Tape.write tape head (machineRouting245.transition
            (oldStateRouting245 68) (Tape.read tape head)).write)
          ((machineRouting245.transition (oldStateRouting245 68)
            (Tape.read tape head)).move.apply head - 2) = true
        rw [hb, row68_true]
        change Tape.read (Tape.write tape head true) (head + 1 - 2) = true
        rw [show head + 1 - 2 = head - 1 by omega,
          Tape.read_write_of_ne tape (by omega : head - 1 ≠ head) true]
        exact hprior
      · change Tape.read
          (Tape.write tape head (machineRouting245.transition
            (oldStateRouting245 123) (Tape.read tape head)).write)
          ((machineRouting245.transition (oldStateRouting245 123)
            (Tape.read tape head)).move.apply head - 1) = true at hleft
        rw [hb, row123_false] at hleft
        change Tape.read (Tape.write tape head false) (head + 1 - 1) = true at hleft
        rw [show head + 1 - 1 = head by omega, Tape.read_write_same] at hleft
        cases hleft
    · intro hn
      change (machineRouting245.transition q (Tape.read tape head)).next =
        some (oldStateRouting245 167) at hn
      have ha := into167_action q (Tape.read tape head) hn
      change Tape.read
        (Tape.write tape head (machineRouting245.transition q (Tape.read tape head)).write)
        ((machineRouting245.transition q (Tape.read tape head)).move.apply head - 1) = true
      rw [ha]
      change Tape.read (Tape.write tape head true) (head + 1 - 1) = true
      rw [show head + 1 - 1 = head by omega]
      exact Tape.read_write_same tape head true

/-- No fixed fuel: every natural continuation preserves the original invariant. -/
theorem runFrom_holds (c : Config 245) (hc : Holds c) (t : Nat) :
    Holds (machineRouting245.runFrom c t) := by
  induction t with
  | zero => exact hc
  | succ t ih => exact step_holds (machineRouting245.runFrom c t) ih

/-- Every point of the original blank run satisfies the invariant. -/
theorem run_holds (t : Nat) : Holds (machineRouting245.run t) := by
  induction t with
  | zero => exact initial_holds
  | succ t ih => exact step_holds (machineRouting245.run t) ih

end SetTheory.BusyBeaver.ZFC.Routing245Invariant
