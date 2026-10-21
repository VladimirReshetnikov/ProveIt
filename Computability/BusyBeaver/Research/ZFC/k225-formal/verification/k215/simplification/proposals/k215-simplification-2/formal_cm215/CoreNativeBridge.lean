import BusyBeaver.Core
import MarkerTransfer

/-! Synchronous embedding of the repository's finite-support dense machines
into the full-function tape semantics used by the local marker theorem. -/
namespace CoreNativeBridge

open SetTheory.BusyBeaver
open MarkerTransfer

def label {n : Nat} (ex : Fin n → Q) (halt : Q) : Option (Fin n) → Q
  | none => halt
  | some q => ex q

def embed {n : Nat} (ex : Fin n → Q) (halt : Q) (c : Config n) : Conf :=
  ⟨label ex halt c.state, c.head, fun x => SetTheory.BusyBeaver.Tape.read c.tape x⟩

def Compatible {n : Nat} (D : Machine n) (M : TM) (ex : Fin n → Q) (halt : Q) : Prop :=
  ∀ q b, M (ex q) b = some
    ⟨(D.transition q b).write, decide ((D.transition q b).move = .right),
      label ex halt (D.transition q b).next⟩

theorem read_write (t : SetTheory.BusyBeaver.Tape) (h : Int) (b : Bool) :
    (fun x => SetTheory.BusyBeaver.Tape.read (SetTheory.BusyBeaver.Tape.write t h b) x) =
    MarkerTransfer.write (fun x => SetTheory.BusyBeaver.Tape.read t x) h b := by
  funext x
  by_cases hx : x = h
  · subst x
    simp [MarkerTransfer.write]
  · simp [MarkerTransfer.write, hx, SetTheory.BusyBeaver.Tape.read_write_of_ne _ hx]

theorem embed_step {n : Nat} {D : Machine n} {M : TM} {ex : Fin n → Q} {halt : Q}
    (hrows : Compatible D M ex halt) (hhalt : ∀ b, M halt b = none) (c : Config n) :
    embed ex halt (D.step c) = MarkerTransfer.next M (embed ex halt c) := by
  rcases c with ⟨q, h, t⟩
  cases q with
  | none => simp [Machine.step, embed, label, MarkerTransfer.next, hhalt]
  | some q =>
      have hr := hrows q (SetTheory.BusyBeaver.Tape.read t h)
      unfold embed Machine.step MarkerTransfer.next label
      simp only [hr]
      generalize D.transition q (SetTheory.BusyBeaver.Tape.read t h) = a
      rcases a with ⟨w, mv, z⟩
      cases mv <;> simp [Move.apply, delta, read_write, Int.sub_eq_add_neg, label]

theorem halt_embed {n : Nat} {D : Machine n} {M : TM} {ex : Fin n → Q} {halt : Q}
    (hrows : Compatible D M ex halt) (hhalt : ∀ b, M halt b = none) (c : Config n) :
    MarkerTransfer.Halt M (embed ex halt c) ↔ c.state = none := by
  rcases c with ⟨q, h, t⟩
  cases q with
  | none => simp [embed, label, MarkerTransfer.Halt, hhalt]
  | some q =>
      have hr := hrows q (SetTheory.BusyBeaver.Tape.read t h)
      simp [embed, label, MarkerTransfer.Halt, hr]

theorem embed_run {n : Nat} {D : Machine n} {M : TM} {ex : Fin n → Q} {halt : Q}
    (hrows : Compatible D M ex halt) (hhalt : ∀ b, M halt b = none) (k : Nat) :
    embed ex halt (D.run k) =
    PositiveSimulation.iter (MarkerTransfer.next M) k (embed ex halt (initial n)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Machine.run, embed_step hrows hhalt, ih]
      rfl

/-- A dense machine and its exact sparse labeling halt at the same time. -/
theorem blank_iff {n : Nat} {D : Machine (n + 1)} {M : TM}
    {ex : Fin (n + 1) → Q} {halt : Q}
    (hrows : Compatible D M ex halt) (hhalt : ∀ b, M halt b = none)
    (hstart : ex 0 = 0) :
    (∃ k, (D.run k).state = none) ↔
    ∃ k, MarkerTransfer.Halt M
      (PositiveSimulation.iter (MarkerTransfer.next M) k ⟨0, 0, fun _ => false⟩) := by
  have hz : embed ex halt (initial (n + 1)) = ⟨0, 0, fun _ => false⟩ := by
    simp [embed, initial, startState, label, hstart, SetTheory.BusyBeaver.Tape.read]
  have hk (k : Nat) := halt_embed hrows hhalt (D.run k)
  simp only [embed_run hrows hhalt, hz] at hk
  constructor
  · rintro ⟨k, h⟩
    exact ⟨k, (hk k).mpr h⟩
  · rintro ⟨k, h⟩
    exact ⟨k, (hk k).mp h⟩

#print axioms blank_iff
end CoreNativeBridge
