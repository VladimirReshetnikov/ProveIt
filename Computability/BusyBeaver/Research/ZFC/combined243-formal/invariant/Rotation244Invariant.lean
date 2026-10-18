import BusyBeaver.ZFC.TableRotation244

/-!
The local predecessor invariant for the rotated244 table.
This is a source-only port of the checked original Routing245 invariant.
Its incoming rows68/81/167 are unchanged by the QT rotation.
Every Core configuration (arbitrary finite-support tape) and natural duration
is quantified; no register-frame or runtime hypothesis is introduced.
The new table/provider and this port await independent kernel checking.
-/
namespace SetTheory.BusyBeaver.ZFC.Rotation244Invariant

/-- The old68 and old167 entries have a one immediately to their left.
At old81 a left one entails a second one two cells to the left. -/
def Holds (c : Config 244) : Prop :=
  (c.state = some (oldStateRotation244 68) →
    Tape.read c.tape (c.head - 1) = true) ∧
  (c.state = some (oldStateRotation244 81) →
    Tape.read c.tape (c.head - 1) = true →
      Tape.read c.tape (c.head - 2) = true) ∧
  (c.state = some (oldStateRotation244 167) →
    Tape.read c.tape (c.head - 1) = true)

/-- Both incoming rows write one and move right. -/
private theorem into68_action : ∀ (q : Fin 244) (b : Bool),
    (machineRotation244.transition q b).next = some (oldStateRotation244 68) →
      machineRotation244.transition q b =
        ⟨true, .right, some (oldStateRotation244 68)⟩ := by
  decide +kernel

/-- Both incoming rows write one and move right. -/
private theorem into167_action : ∀ (q : Fin 244) (b : Bool),
    (machineRotation244.transition q b).next = some (oldStateRotation244 167) →
      machineRotation244.transition q b =
        ⟨true, .right, some (oldStateRotation244 167)⟩ := by
  decide +kernel

private theorem into81_cases : ∀ (q : Fin 244) (b : Bool),
    (machineRotation244.transition q b).next = some (oldStateRotation244 81) →
      (q = oldStateRotation244 68 ∧ b = true) ∨
      (q = oldStateRotation244 123 ∧ b = false) := by
  decide +kernel

private theorem row68_true :
    machineRotation244.transition (oldStateRotation244 68) true =
      ⟨true, .right, some (oldStateRotation244 81)⟩ := by decide +kernel

private theorem row123_false :
    machineRotation244.transition (oldStateRotation244 123) false =
      ⟨false, .right, some (oldStateRotation244 81)⟩ := by decide +kernel

private theorem start_distinct :
    oldStateRotation244 95 ≠ oldStateRotation244 68 ∧
      oldStateRotation244 95 ≠ oldStateRotation244 81 ∧
      oldStateRotation244 95 ≠ oldStateRotation244 167 := by decide +kernel

/-- The invariant is vacuous at the shared start for arbitrary head and tape. -/
theorem start_holds (head : Int) (tape : Tape) :
    Holds ⟨some (oldStateRotation244 95), head, tape⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    exact False.elim (start_distinct.1 (Option.some.inj hs))
  · intro hs
    exact False.elim (start_distinct.2.1 (Option.some.inj hs))
  · intro hs
    exact False.elim (start_distinct.2.2 (Option.some.inj hs))

/-- Literal canonical state zero, head zero and the all-zero tape. -/
theorem initial_holds : Holds (initial 244) := by
  change Holds ⟨some (oldStateRotation244 95), 0, []⟩
  exact start_holds 0 []

/-- The finite incoming-row facts preserve the invariant in one literal step.
Already halted configurations are stationary and are included. -/
theorem step_holds (c : Config 244) (hc : Holds c) :
    Holds (machineRotation244.step c) := by
  rcases c with ⟨state, head, tape⟩
  cases state with
  | none => exact hc
  | some q =>
    refine ⟨?_, ?_, ?_⟩
    · intro hn
      change (machineRotation244.transition q (Tape.read tape head)).next =
        some (oldStateRotation244 68) at hn
      have ha := into68_action q (Tape.read tape head) hn
      change Tape.read
        (Tape.write tape head (machineRotation244.transition q (Tape.read tape head)).write)
        ((machineRotation244.transition q (Tape.read tape head)).move.apply head - 1) = true
      rw [ha]
      change Tape.read (Tape.write tape head true) (head + 1 - 1) = true
      rw [show head + 1 - 1 = head by omega]
      exact Tape.read_write_same tape head true
    · intro hn hleft
      change (machineRotation244.transition q (Tape.read tape head)).next =
        some (oldStateRotation244 81) at hn
      rcases into81_cases q (Tape.read tape head) hn with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · have hprior : Tape.read tape (head - 1) = true := hc.1 rfl
        change Tape.read
          (Tape.write tape head (machineRotation244.transition
            (oldStateRotation244 68) (Tape.read tape head)).write)
          ((machineRotation244.transition (oldStateRotation244 68)
            (Tape.read tape head)).move.apply head - 2) = true
        rw [hb, row68_true]
        change Tape.read (Tape.write tape head true) (head + 1 - 2) = true
        rw [show head + 1 - 2 = head - 1 by omega,
          Tape.read_write_of_ne tape (by omega : head - 1 ≠ head) true]
        exact hprior
      · change Tape.read
          (Tape.write tape head (machineRotation244.transition
            (oldStateRotation244 123) (Tape.read tape head)).write)
          ((machineRotation244.transition (oldStateRotation244 123)
            (Tape.read tape head)).move.apply head - 1) = true at hleft
        rw [hb, row123_false] at hleft
        change Tape.read (Tape.write tape head false) (head + 1 - 1) = true at hleft
        rw [show head + 1 - 1 = head by omega, Tape.read_write_same] at hleft
        cases hleft
    · intro hn
      change (machineRotation244.transition q (Tape.read tape head)).next =
        some (oldStateRotation244 167) at hn
      have ha := into167_action q (Tape.read tape head) hn
      change Tape.read
        (Tape.write tape head (machineRotation244.transition q (Tape.read tape head)).write)
        ((machineRotation244.transition q (Tape.read tape head)).move.apply head - 1) = true
      rw [ha]
      change Tape.read (Tape.write tape head true) (head + 1 - 1) = true
      rw [show head + 1 - 1 = head by omega]
      exact Tape.read_write_same tape head true

/-- No fixed fuel: every natural continuation preserves the original invariant. -/
theorem runFrom_holds (c : Config 244) (hc : Holds c) (t : Nat) :
    Holds (machineRotation244.runFrom c t) := by
  induction t with
  | zero => exact hc
  | succ t ih => exact step_holds (machineRotation244.runFrom c t) ih

/-- Every point of the original blank run satisfies the invariant. -/
theorem run_holds (t : Nat) : Holds (machineRotation244.run t) := by
  induction t with
  | zero => exact initial_holds
  | succ t ih => exact step_holds (machineRotation244.run t) ih

end SetTheory.BusyBeaver.ZFC.Rotation244Invariant
