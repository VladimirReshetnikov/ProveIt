import BusyBeaver.Core

/-!
Exact state quotients for the repository's two-symbol, bi-infinite-tape model.

The transition hypothesis is precisely what partition refinement checks:
writing and movement agree, and successor states agree after applying the
state map. No injectivity or surjectivity of that map is needed. All finite
runs commute with it, so blank-tape halting and the final score agree in both
directions. This proves the generic reduction rule; it does not certify the
Python auditor, its window/macro search, or a ZFC consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC

universe u v

/-- Map only the operational state of an action. -/
def mapAction {Q : Type u} {R : Type v} (f : Q → R)
    (action : TypedAction Q) : TypedAction R where
  write := action.write
  move := action.move
  next := action.next.map f

/-- Preserve the head and tape, including the halted-state convention. -/
def mapConfig {Q : Type u} {R : Type v} (f : Q → R)
    (cfg : TypedConfig Q) : TypedConfig R where
  state := cfg.state.map f
  head := cfg.head
  tape := cfg.tape

/-- A directly checkable transition certificate for a state quotient. -/
def TransitionQuotient {Q : Type u} {R : Type v} (f : Q → R)
    (original : TypedMachine Q) (reduced : TypedMachine R) : Prop :=
  ∀ q bit, reduced.transition (f q) bit = mapAction f (original.transition q bit)

theorem step_map {Q : Type u} {R : Type v} {f : Q → R}
    {original : TypedMachine Q} {reduced : TypedMachine R}
    (certificate : TransitionQuotient f original reduced) (cfg : TypedConfig Q) :
    reduced.step (mapConfig f cfg) = mapConfig f (original.step cfg) := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => rfl
      | some q =>
          dsimp only [TypedMachine.step, mapConfig, Option.map]
          rw [certificate q (Tape.read tape head)]
          rfl

theorem runFrom_map {Q : Type u} {R : Type v} {f : Q → R}
    {original : TypedMachine Q} {reduced : TypedMachine R}
    (certificate : TransitionQuotient f original reduced) (cfg : TypedConfig Q) :
    ∀ steps,
      reduced.runFrom (mapConfig f cfg) steps =
        mapConfig f (original.runFrom cfg steps)
  | 0 => rfl
  | steps + 1 => by
      change reduced.step (reduced.runFrom (mapConfig f cfg) steps) =
        mapConfig f (original.step (original.runFrom cfg steps))
      rw [runFrom_map certificate cfg steps]
      exact step_map certificate (original.runFrom cfg steps)

theorem run_map {Q : Type u} {R : Type v} {f : Q → R}
    {original : TypedMachine Q} {reduced : TypedMachine R}
    (certificate : TransitionQuotient f original reduced) (start : Q) :
    ∀ steps,
      reduced.run (f start) steps = mapConfig f (original.run start steps)
  | 0 => rfl
  | steps + 1 => by
      change reduced.step (reduced.run (f start) steps) =
        mapConfig f (original.step (original.run start steps))
      rw [run_map certificate start steps]
      exact step_map certificate (original.run start steps)

theorem mapped_state_none_iff {Q : Type u} {R : Type v} (f : Q → R)
    (cfg : TypedConfig Q) :
    (mapConfig f cfg).state = none ↔ cfg.state = none := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => constructor <;> intro _ <;> rfl
      | some q => constructor <;> intro h <;> cases h

/-- Halting from an arbitrary tape, without imposing a score. -/
def HaltsFrom {Q : Type u} (machine : TypedMachine Q) (cfg : TypedConfig Q) : Prop :=
  ∃ steps, (machine.runFrom cfg steps).state = none

/-- Blank-tape halting at the explicitly chosen start state. -/
def Halts {Q : Type u} (machine : TypedMachine Q) (start : Q) : Prop :=
  ∃ steps, (machine.run start steps).state = none

theorem haltsFrom_iff {Q : Type u} {R : Type v} {f : Q → R}
    {original : TypedMachine Q} {reduced : TypedMachine R}
    (certificate : TransitionQuotient f original reduced) (cfg : TypedConfig Q) :
    HaltsFrom reduced (mapConfig f cfg) ↔ HaltsFrom original cfg := by
  constructor
  · rintro ⟨steps, halted⟩
    rw [runFrom_map certificate] at halted
    exact ⟨steps, (mapped_state_none_iff f _).mp halted⟩
  · rintro ⟨steps, halted⟩
    refine ⟨steps, ?_⟩
    rw [runFrom_map certificate]
    exact (mapped_state_none_iff f _).mpr halted

theorem halts_iff {Q : Type u} {R : Type v} {f : Q → R}
    {original : TypedMachine Q} {reduced : TypedMachine R}
    (certificate : TransitionQuotient f original reduced) (start : Q) :
    Halts reduced (f start) ↔ Halts original start := by
  constructor
  · rintro ⟨steps, halted⟩
    rw [run_map certificate] at halted
    exact ⟨steps, (mapped_state_none_iff f _).mp halted⟩
  · rintro ⟨steps, halted⟩
    refine ⟨steps, ?_⟩
    rw [run_map certificate]
    exact (mapped_state_none_iff f _).mpr halted

/-- A quotient also preserves the exact final Busy Beaver score. -/
theorem haltsWithScore_iff {Q : Type u} {R : Type v} {f : Q → R}
    {original : TypedMachine Q} {reduced : TypedMachine R}
    (certificate : TransitionQuotient f original reduced) (start : Q) (score : Nat) :
    reduced.HaltsWithScore (f start) score ↔ original.HaltsWithScore start score := by
  constructor
  · rintro ⟨steps, halted, scored⟩
    rw [run_map certificate] at halted scored
    exact ⟨steps, (mapped_state_none_iff f _).mp halted, scored⟩
  · rintro ⟨steps, halted, scored⟩
    refine ⟨steps, ?_, ?_⟩
    · rw [run_map certificate]
      exact (mapped_state_none_iff f _).mpr halted
    · rw [run_map certificate]
      exact scored

#print axioms halts_iff
#print axioms haltsWithScore_iff

end SetTheory.BusyBeaver.ZFC
