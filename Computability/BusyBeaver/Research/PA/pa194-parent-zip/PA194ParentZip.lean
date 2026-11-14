import PA194ZipBridge
import PA194Control
import PA195GenericTrace

/-! Full-tape/zipper synchronization for the PA194 unfolded parent table.
This concerns ordinary finite runs, not an internal PRA proof. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194ParentZip
open PA194LocalQuotient PA194ZipBridge

/-- The same row lookup used by the parent register runtime. -/
def rowMachine (rows : List Row) (q : Nat) (bit : Bool) : Option (Bool × Bool × Nat) :=
  (lookup rows q bit).map fun r => (r.write, r.right, r.target)

def Sync (a : Option Configuration) (z : Option M6.Zip.Conf) : Prop :=
  match a, z with
  | none, none => True
  | some a, some z => Related a z
  | _, _ => False

theorem read_head (a : Configuration) (z : M6.Zip.Conf) (h : Related a z) :
    a.tape a.pos = z.r.headD false := by
  have h0 := h.2 0
  have heq : z.r.getD 0 false = z.r.headD false := by cases z.r <;> rfl
  change a.tape (a.pos + 0) = z.r.getD 0 false at h0
  have h0' : a.tape a.pos = z.r.getD 0 false := by simpa using h0
  exact h0'.trans heq

theorem step_sync (rows : List Row) (a : Configuration) (z : M6.Zip.Conf)
    (h : Related a z) : Sync (fullStep rows a) (M6.Zip.step (rowMachine rows) z) := by
  have he : a.state = z.q := h.1
  have hb : a.tape a.pos = z.r.headD false := read_head a z h
  cases hr : lookup rows a.state (a.tape a.pos) with
  | none =>
    have hm : rowMachine rows z.q (z.r.headD false) = none := by
      unfold rowMachine
      rw [← he, ← hb, hr]
      rfl
    simp only [Sync, fullStep, hr, M6.Zip.step, hm]
    trivial
  | some r =>
    have hm : rowMachine rows z.q (z.r.headD false) = some (r.write, r.right, r.target) := by
      unfold rowMachine
      rw [← he, ← hb, hr]
      rfl
    cases r with
    | mk state read write right target =>
      cases right <;>
        simp only [Sync, fullStep, hr, M6.Zip.step, hm] <;>
        exact related_advance a z h write _ target

theorem run_sync (rows : List Row) (n : Nat) (a : Configuration) (z : M6.Zip.Conf)
    (h : Related a z) : Sync (fullRun rows n a) (M6.Zip.run (rowMachine rows) n z) := by
  induction n generalizing a z with
  | zero => exact h
  | succ n ih =>
    have hs := step_sync rows a z h
    cases ha : fullStep rows a with
    | none =>
      cases hz : M6.Zip.step (rowMachine rows) z with
      | none => simp [fullRun, M6.Zip.run, ha, hz, Sync]
      | some z' => simp [ha, hz, Sync] at hs
    | some a' =>
      cases hz : M6.Zip.step (rowMachine rows) z with
      | none => simp [ha, hz, Sync] at hs
      | some z' =>
        have hrel : Related a' z' := by simpa [ha, hz, Sync] using hs
        simpa [fullRun, M6.Zip.run, ha, hz] using ih a' z' hrel

/-- Stuck-state halting agrees for arbitrary rows and related initial tapes. -/
theorem halts_iff_zip (rows : List Row) (a : Configuration) (z : M6.Zip.Conf)
    (hrel : Related a z) :
    (∃ n b, fullRun rows n a = some b ∧ fullStep rows b = none) ↔
      M6.Zip.Halts (rowMachine rows) z := by
  constructor
  · rintro ⟨n, b, hb, hstop⟩
    have hs := run_sync rows n a z hrel
    cases hz : M6.Zip.run (rowMachine rows) n z with
    | none => simp [hb, hz, Sync] at hs
    | some z' =>
      have hr : Related b z' := by simpa [hb, hz, Sync] using hs
      have hstep := step_sync rows b z' hr
      cases hh : M6.Zip.step (rowMachine rows) z' with
      | none => exact ⟨z', ⟨n, hz⟩, hh⟩
      | some _ => simp [hstop, hh, Sync] at hstep
  · rintro ⟨z', ⟨n, hz⟩, hstop⟩
    have hs := run_sync rows n a z hrel
    cases hb : fullRun rows n a with
    | none => simp [hb, hz, Sync] at hs
    | some b =>
      have hr : Related b z' := by simpa [hb, hz, Sync] using hs
      have hstep := step_sync rows b z' hr
      cases hh : fullStep rows b with
      | none => exact ⟨n, b, hb, hh⟩
      | some _ => simp [hh, hstop, Sync] at hstep

theorem parent_halt_stuck (c : Configuration) (h : c.state = 254) :
    fullStep parent c = none := by
  have h0 : lookup parent 254 false = none := by decide +kernel
  have h1 : lookup parent 254 true = none := by decide +kernel
  cases hb : c.tape c.pos <;> simp [fullStep, h, hb, h0, h1]

theorem parent_stuck_iff (c : Configuration) (hv : validControl c.state) :
    fullStep parent c = none ↔ c.state = 254 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨d, hd⟩ := parent_total c hv hn
    rw [h] at hd
    contradiction
  · exact parent_halt_stuck c

theorem parent_run_valid (n : Nat) (a b : Configuration) (hv : validControl a.state)
    (h : fullRun parent n a = some b) : validControl b.state := by
  induction n generalizing a with
  | zero =>
    simp only [fullRun, Option.some.injEq] at h
    subst b
    exact hv
  | succ n ih =>
    cases hs : fullStep parent a with
    | none => simp [fullRun, hs] at h
    | some c =>
      have hc := parent_step_valid a c hs
      have hr : fullRun parent n c = some b := by simpa [fullRun, hs] using h
      exact ih c hc hr

theorem generic_eq_fullRun (rows : List Row) (n : Nat) (c : Configuration) :
    PA195GenericTrace.run (fullStep rows) n c = fullRun rows n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [PA195GenericTrace.run, fullRun]
    cases hs : fullStep rows c with
    | none => rfl
    | some d => simpa [hs] using ih d

/-- For a valid parent control, reaching halt 254 is equivalent to the
    corresponding zipper machine becoming stuck. -/
theorem parent_halts_iff_zip (a : Configuration) (z : M6.Zip.Conf)
    (hrel : Related a z) (hv : validControl a.state) :
    PA195GenericTrace.Halts (fullStep parent) (fun c => c.state = 254) a ↔
      M6.Zip.Halts (rowMachine parent) z := by
  rw [← halts_iff_zip parent a z hrel]
  constructor
  · rintro ⟨n, b, hb, hh⟩
    rw [generic_eq_fullRun] at hb
    exact ⟨n, b, hb, parent_halt_stuck b hh⟩
  · rintro ⟨n, b, hb, hh⟩
    have hbvalid := parent_run_valid n a b hv hb
    exact ⟨n, b, by rw [generic_eq_fullRun]; exact hb,
      (parent_stuck_iff b hbvalid).mp hh⟩

#print axioms step_sync
#print axioms run_sync
#print axioms halts_iff_zip
#print axioms parent_halts_iff_zip
end PA194ParentZip
