import BusyBeaver.ZFC.KDense215
import CM215Invariant
import PositiveStutter

/-! A bridge from ProveIt's exact dense machine semantics to the
function-tape semantics used by the small CM215 transfer proof. -/

namespace CM215.CoreBridge

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC

def label : Option (Fin 215) → CM215.State
  | none => 215
  | some q => ⟨q.val, Nat.lt_trans q.isLt (by decide)⟩

def embed (c : SetTheory.BusyBeaver.Config 215) : CM215.Config :=
  ⟨label c.state, c.head, Tape.read c.tape⟩

def action (a : SetTheory.BusyBeaver.Action 215) : CM215.Action :=
  ⟨a.write, decide (a.move = .right), label a.next⟩

def partialStep (M : Machine 215) (c : SetTheory.BusyBeaver.Config 215) :
    Option (SetTheory.BusyBeaver.Config 215) :=
  match c.state with
  | none => none
  | some _ => some (M.step c)

theorem partial_none (M : Machine 215) (c : SetTheory.BusyBeaver.Config 215) :
    partialStep M c = none ↔ c.state = none := by
  unfold partialStep
  cases c.state <;> simp

theorem tape_write (t : SetTheory.BusyBeaver.Tape) (h : Int) (w : Bool) :
    CM215.write (Tape.read t) h w = Tape.read (Tape.write t h w) := by
  funext x
  by_cases hx : x = h
  · subst x
    simp
  · simp [CM215.write, hx, Tape.read_write_of_ne t hx]

def Commutes (M : Machine 215) (d : CM215.State → Bool → Option CM215.Action) : Prop :=
  (∀ q : Fin 215, ∀ b, d (label (some q)) b = some (action (M.transition q b))) ∧
  (∀ b, d (label none) b = none)

theorem step_embed {M : Machine 215} {d : CM215.State → Bool → Option CM215.Action}
    (hC : Commutes M d) (c : SetTheory.BusyBeaver.Config 215) :
    CM215.step d (embed c) = (partialStep M c).map embed := by
  cases hc : c.state with
  | none => simp [CM215.step, embed, partialStep, hc, hC.2]
  | some q =>
    simp only [CM215.step, embed, hc, hC.1, Option.map_some, partialStep]
    apply congrArg some
    simp only [CM215.act, action, Machine.step, hc]
    rw [tape_write]
    generalize M.transition q (Tape.read c.tape c.head) = a
    cases a with
    | mk w mv nx =>
      cases mv <;> simp [CM215.move, Move.apply, Int.sub_eq_add_neg]

theorem simulation {M : Machine 215} {d : CM215.State → Bool → Option CM215.Action}
    (hC : Commutes M d) :
    PositiveStutter.Simulation (partialStep M) (CM215.step d)
      (fun c z => z = embed c) := by
  constructor
  · intro c z hz
    subst z
    rw [step_embed hC]
    exact Option.map_eq_none_iff.symm
  · intro c z c' hz hs
    subst z
    refine ⟨1, embed c', by decide, ?_, rfl⟩
    simp only [PositiveStutter.run, step_embed hC, hs, Option.map_some, Option.bind_some]

theorem runFrom_first (M : Machine 215) (c : SetTheory.BusyBeaver.Config 215) (n : Nat) :
    M.runFrom c (n + 1) = M.runFrom (M.step c) n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Machine.runFrom] using congrArg M.step ih

theorem partial_run_matches (M : Machine 215) (n : Nat)
    (c d : SetTheory.BusyBeaver.Config 215)
    (h : PositiveStutter.run (partialStep M) n c = some d) : M.runFrom c n = d := by
  induction n generalizing c with
  | zero => exact Option.some.inj h
  | succ n ih =>
    cases hc : c.state with
    | none => simp [PositiveStutter.run, partialStep, hc] at h
    | some q =>
      simp only [PositiveStutter.run, partialStep, hc, Option.bind_some] at h
      rw [runFrom_first]
      exact ih (M.step c) h

theorem partial_halts_iff (M : Machine 215) (c : SetTheory.BusyBeaver.Config 215) :
    PositiveStutter.Halts (partialStep M) c ↔ ∃ n, (M.runFrom c n).state = none := by
  constructor
  · rintro ⟨n, d, hr, hd⟩
    exact ⟨n, (partial_run_matches M n c d hr) ▸ ((partial_none M d).mp hd)⟩
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero => exact PositiveStutter.halt_now ((partial_none M c).mpr hn)
    | succ n ih =>
      cases hc : c.state with
      | none => exact PositiveStutter.halt_now ((partial_none M c).mpr hc)
      | some q =>
        rw [runFrom_first] at hn
        apply PositiveStutter.halts_of_run (n := 1) (c := c) (d := M.step c)
        · simp [PositiveStutter.run, partialStep, hc]
        · exact ih (M.step c) hn

theorem run_initial (M : Machine 215) (n : Nat) : M.runFrom (initial 215) n = M.run n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Machine.runFrom, Machine.run] using congrArg M.step ih

theorem blank_iff {M : Machine 215} {d : CM215.State → Bool → Option CM215.Action}
    (hC : Commutes M d) : KDenseBridge.BlankHalts M ↔
    PositiveStutter.Halts (CM215.step d) ⟨0, 0, fun _ => false⟩ := by
  have hs := (simulation hC).halts_iff (a := initial 215) (b := embed (initial 215)) rfl
  rw [partial_halts_iff] at hs
  have he : embed (initial 215) = (⟨0, 0, fun _ => false⟩ : CM215.Config) := rfl
  rw [he] at hs
  simpa only [KDenseBridge.BlankHalts, run_initial] using hs

theorem old_commutes : Commutes KDense215.machine215 CM215.old := by
  constructor <;> decide +kernel

/-- The old table in the small certificate is the *exact* formally calibrated
dense K215 table under the repository's blank-halting semantics. -/
theorem old_blank_iff : KDenseBridge.BlankHalts KDense215.machine215 ↔
    PositiveStutter.Halts (CM215.step CM215.old) ⟨0, 0, fun _ => false⟩ :=
  blank_iff old_commutes

#print axioms old_blank_iff

end CM215.CoreBridge
