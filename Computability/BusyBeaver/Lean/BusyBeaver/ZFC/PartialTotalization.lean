import BusyBeaver.Core

/-!
An undefined transition can be replaced by a tape-preserving Rado halt action.
The extra final head move is allowed: both runs have the same state and tape
at every time, and their heads agree whenever the state is operational.
Here an attempted undefined transition consumes one source step and changes
the source state to halted in place. Under a convention that halts before
attempting that step, totalization instead needs one extra final action.

This generic theorem justifies the normalization convention used for the
experimental 252-state table. It does not verify the Python normalizer, its
parsers, the specific generated rows, or any consistency calibration.
-/

namespace SetTheory.BusyBeaver.ZFC.PartialTotalization

universe u

structure PartialMachine (Q : Type u) where
  transition : Q → Bool → Option (TypedAction Q)

namespace PartialMachine

def step {Q : Type u} (M : PartialMachine Q) (cfg : TypedConfig Q) : TypedConfig Q :=
  match cfg.state with
  | none => cfg
  | some q =>
      match M.transition q (Tape.read cfg.tape cfg.head) with
      | none => { cfg with state := none }
      | some action =>
          { state := action.next
            head := action.move.apply cfg.head
            tape := Tape.write cfg.tape cfg.head action.write }

def totalize {Q : Type u} (M : PartialMachine Q) : TypedMachine Q where
  transition q bit :=
    match M.transition q bit with
    | some action => action
    | none => { write := bit, move := .right, next := none }

def runFrom {Q : Type u} (M : PartialMachine Q) (cfg : TypedConfig Q) : Nat → TypedConfig Q
  | 0 => cfg
  | t + 1 => M.step (M.runFrom cfg t)

def run {Q : Type u} (M : PartialMachine Q) (start : Q) : Nat → TypedConfig Q :=
  M.runFrom { state := some start, head := 0, tape := [] }

def HaltsWithScore {Q : Type u} (M : PartialMachine Q) (start : Q) (score : Nat) : Prop :=
  ∃ t, (M.run start t).state = none ∧ (M.run start t).tape.length = score

end PartialMachine

def Related {Q : Type u} (old new : TypedConfig Q) : Prop :=
  old.state = new.state ∧ old.tape = new.tape ∧
    (old.state ≠ none → old.head = new.head)

theorem related_refl {Q : Type u} (cfg : TypedConfig Q) : Related cfg cfg := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

theorem related_live_eq {Q : Type u} {old new : TypedConfig Q}
    (h : Related old new) (live : old.state ≠ none) : old = new := by
  cases old with
  | mk os oh ot =>
      cases new with
      | mk ns nh nt =>
          rcases h with ⟨hs, ht, hh⟩
          have hhead := hh live
          dsimp at hs ht hhead
          cases hs
          cases ht
          cases hhead
          rfl

theorem step_related {Q : Type u} (M : PartialMachine Q)
    {old new : TypedConfig Q} (h : Related old new) :
    Related (M.step old) (M.totalize.step new) := by
  by_cases live : old.state = none
  · have hn : new.state = none := h.1.symm.trans live
    simpa only [PartialMachine.step, TypedMachine.step, live, hn] using h
  · have heq := related_live_eq h live
    subst new
    cases old with
    | mk state head tape =>
        cases state with
        | none => exact False.elim (live rfl)
        | some q =>
            cases ha : M.transition q (Tape.read tape head) with
            | none =>
                simp [PartialMachine.step, PartialMachine.totalize, TypedMachine.step,
                      ha, Related]
            | some action =>
                simp [PartialMachine.step, PartialMachine.totalize, TypedMachine.step,
                      ha, Related]

theorem runFrom_related {Q : Type u} (M : PartialMachine Q) (cfg : TypedConfig Q) :
    ∀ t, Related (M.runFrom cfg t) (M.totalize.runFrom cfg t)
  | 0 => related_refl cfg
  | t + 1 => step_related M (runFrom_related M cfg t)

theorem run_state_eq {Q : Type u} (M : PartialMachine Q) (start : Q) (t : Nat) :
    (M.totalize.run start t).state = (M.run start t).state := by
  rw [TypedMachine.run_eq_runFrom]
  exact (runFrom_related M _ t).1.symm

theorem run_tape_eq {Q : Type u} (M : PartialMachine Q) (start : Q) (t : Nat) :
    (M.totalize.run start t).tape = (M.run start t).tape := by
  rw [TypedMachine.run_eq_runFrom]
  exact (runFrom_related M _ t).2.1.symm

theorem haltsWithScore_iff {Q : Type u} (M : PartialMachine Q) (start : Q) (score : Nat) :
    M.totalize.HaltsWithScore start score ↔ M.HaltsWithScore start score := by
  simp only [TypedMachine.HaltsWithScore, PartialMachine.HaltsWithScore,
             run_state_eq, run_tape_eq]

theorem halts_iff {Q : Type u} (M : PartialMachine Q) (start : Q) :
    (∃ t, (M.totalize.run start t).state = none) ↔
      (∃ t, (M.run start t).state = none) := by
  simp only [run_state_eq]

#print axioms halts_iff
#print axioms haltsWithScore_iff

end SetTheory.BusyBeaver.ZFC.PartialTotalization
