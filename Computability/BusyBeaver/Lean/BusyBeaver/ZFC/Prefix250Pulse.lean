import BusyBeaver.ZFC.TablePrefix250
import BusyBeaver.ZFC.ZipperRuns

/-!
The pulse gadget and safe reuse of its initial-state zero row.

Source-only draft: no compiler invocation has been performed in this lane.
The two three-transition identities hold in arbitrary finite zipper contexts
and transfer to the existing complete-tape Core semantics via `ZipRep`.
The incoming-edge invariant proves that the actual blank run cannot use
old97/read0 after its first transition. No register or consistency endpoint
is claimed here. Attribution and the exact table identity are in TablePrefix250.
-/

namespace SetTheory.BusyBeaver.ZFC.Prefix250Pulse

open FiniteZipper ZipperRuns

private abbrev test := oldStatePrefix250 75
private abbrev pulse := oldStatePrefix250 255
private abbrev entry := oldStatePrefix250 97
private abbrev rollback := oldStatePrefix250 112
private abbrev reverseCarry := oldStatePrefix250 131
private abbrev seed := oldStatePrefix250 83

/-- At the intermediate state, the cell just left of the head is one.
At the reused initial state, the currently scanned cell is one. -/
def PulseSafe {n : Nat} (qPulse qEntry : Fin n) (c : Config n) : Prop :=
  (c.state = some qPulse → Tape.read c.tape (c.head - 1) = true) ∧
  (c.state = some qEntry → Tape.read c.tape c.head = true)

/-- The recurrence invariant only needs the two incoming-edge facts and
those two literal rows. It also handles already halted configurations. -/
theorem pulseSafe_step {n : Nat} (M : Machine n)
    (qTest qPulse qEntry : Fin n)
    (intoPulse : ∀ q b, (M.transition q b).next = some qPulse →
      q = qTest ∧ b = false)
    (intoEntry : ∀ q b, (M.transition q b).next = some qEntry →
      q = qPulse ∧ b = false)
    (testRow : M.transition qTest false = ⟨true, .right, some qPulse⟩)
    (pulseRow : M.transition qPulse false = ⟨true, .left, some qEntry⟩)
    (c : Config n) (hc : PulseSafe qPulse qEntry c) :
    PulseSafe qPulse qEntry (M.step c) := by
  rcases c with ⟨state, head, tape⟩
  cases state with
  | none => exact hc
  | some q =>
    constructor
    · intro hn
      change (M.transition q (Tape.read tape head)).next = some qPulse at hn
      obtain ⟨rfl, hb⟩ := intoPulse q (Tape.read tape head) hn
      simp only [Machine.step, hb, testRow, Move.apply]
      simpa using Tape.read_write_same tape head true
    · intro hn
      change (M.transition q (Tape.read tape head)).next = some qEntry at hn
      obtain ⟨rfl, hb⟩ := intoEntry q (Tape.read tape head) hn
      have hleft : Tape.read tape (head - 1) = true := hc.1 rfl
      simp only [Machine.step, hb, pulseRow, Move.apply]
      rw [Tape.read_write_of_ne tape (by omega : head - 1 ≠ head) true]
      exact hleft

/-- Preservation over every natural duration, without a runtime bound. -/
theorem pulseSafe_runFrom {n : Nat} (M : Machine n)
    (qTest qPulse qEntry : Fin n)
    (intoPulse : ∀ q b, (M.transition q b).next = some qPulse →
      q = qTest ∧ b = false)
    (intoEntry : ∀ q b, (M.transition q b).next = some qEntry →
      q = qPulse ∧ b = false)
    (testRow : M.transition qTest false = ⟨true, .right, some qPulse⟩)
    (pulseRow : M.transition qPulse false = ⟨true, .left, some qEntry⟩)
    (c : Config n) (hc : PulseSafe qPulse qEntry c) (t : Nat) :
    PulseSafe qPulse qEntry (M.runFrom c t) := by
  induction t with
  | zero => exact hc
  | succ t ih =>
    exact pulseSafe_step M qTest qPulse qEntry intoPulse intoEntry
      testRow pulseRow (M.runFrom c t) ih

/-- Complete three-step zero/zero pulse identity on the final table. -/
theorem pulse_zero_zero (h : Int) (l r : List Bool) :
    zipRun machinePrefix250 (zAt test h l (false :: false :: r)) 3 =
      leftAt reverseCarry h l (true :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowPrefix250_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix250_old255_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix250_old97_true]
  simp only [zipRun]
  congr 1
  omega

/-- Complete three-step zero/one rollback identity on the final table. -/
theorem pulse_zero_one (h : Int) (l r : List Bool) :
    zipRun machinePrefix250 (zAt test h l (false :: true :: r)) 3 =
      leftAt rollback h l (false :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowPrefix250_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix250_old255_true,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix250_old131_true]
  simp only [zipRun]
  congr 1
  omega

/-- Both local cases, retaining arbitrary exterior contexts. -/
theorem pulse_zero (b : Bool) (h : Int) (l r : List Bool) :
    zipRun machinePrefix250 (zAt test h l (false :: b :: r)) 3 =
      leftAt (if b then rollback else reverseCarry) h l ((!b) :: true :: r) := by
  cases b with
  | false => exact pulse_zero_zero h l r
  | true => exact pulse_zero_one h l r

/-- The local identity is about actual Core runs and the entire represented
infinite tape, not merely a bounded inspection of the two changed cells. -/
theorem pulse_core {c : Config 250} (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt test h l (false :: b :: r))) :
    ZipRep (machinePrefix250.runFrom c 3)
      (leftAt (if b then rollback else reverseCarry) h l ((!b) :: true :: r)) := by
  have hs := zipRun_sound machinePrefix250 3 hc
  rw [pulse_zero] at hs
  exact hs

/-- Actual canonical start zero writes the one-cell seed. -/
theorem blank_first_step :
    machinePrefix250.run 1 =
      ({ state := some seed, head := 1, tape := [0] } : Config 250) := by
  decide +kernel

private theorem safe_first_step :
    PulseSafe pulse entry (machinePrefix250.run 1) := by
  rw [blank_first_step]
  constructor
  · intro hn
    exact False.elim ((by decide : seed ≠ pulse) (Option.some.inj hn))
  · intro hn
    exact False.elim ((by decide : seed ≠ entry) (Option.some.inj hn))

/-- Every actual blank-run configuration after initialization is pulse-safe. -/
theorem safe_after_first (t : Nat) :
    PulseSafe pulse entry (machinePrefix250.run (t + 1)) := by
  have hs := pulseSafe_runFrom machinePrefix250 test pulse entry
    (fun q b h => (machinePrefix250_into_old255_iff q b).mp h)
    (fun q b h => (machinePrefix250_into_old97_iff q b).mp h)
    rowPrefix250_old75_false rowPrefix250_old255_false
    (machinePrefix250.run 1) safe_first_step t
  rw [← Machine.run_add_eq_runFrom] at hs
  simpa only [Nat.add_comm 1 t] using hs

/-- The reused initial state scans one at every positive runtime occurrence. -/
theorem recurrent_entry_reads_one (t : Nat)
    (hs : (machinePrefix250.run (t + 1)).state = some entry) :
    Tape.read (machinePrefix250.run (t + 1)).tape
      (machinePrefix250.run (t + 1)).head = true :=
  (safe_after_first t).2 hs

/-- The initializer row is used only at the actual initial instant. -/
theorem initializer_only_at_zero (t : Nat)
    (hs : (machinePrefix250.run t).state = some entry)
    (hb : Tape.read (machinePrefix250.run t).tape
      (machinePrefix250.run t).head = false) : t = 0 := by
  cases t with
  | zero => rfl
  | succ t =>
    have ht := recurrent_entry_reads_one t hs
    rw [hb] at ht
    cases ht

end SetTheory.BusyBeaver.ZFC.Prefix250Pulse
