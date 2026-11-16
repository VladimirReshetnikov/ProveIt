module
public import Std.Tactic
@[expose] public section

/-!
The three counter loops preceding S36's sum-one guard. This module proves their
all-natural termination and exact store effect; it does not yet identify the
finite fragment with the published 3,947-leaf source program.
-/
namespace M6.Source.S36Drain

structure Store (Frame : Type) where
  t : Nat
  h : Nat
  x : Nat
  frame : Frame
  deriving DecidableEq

structure Config (Frame : Type) where
  pc : Nat
  store : Store Frame
  deriving DecidableEq

/-- The ten primitive control locations, with 10 the exit. Locations 0, 3 and
7 are decrement-with-zero-test; the other locations are increments or jumps.
The other six source registers are represented by the untouched `frame`. -/
def step (c : Config Frame) : Config Frame :=
  match c.pc with
  | 0 => if c.store.t = 0 then { c with pc := 3 }
         else { c with pc := 1, store.t := c.store.t - 1 }
  | 1 => { c with pc := 2, store.x := c.store.x + 1 }
  | 2 => { c with pc := 0 }
  | 3 => if c.store.h = 0 then { c with pc := 7 }
         else { c with pc := 4, store.h := c.store.h - 1 }
  | 4 => { c with pc := 5, store.t := c.store.t + 1 }
  | 5 => { c with pc := 6, store.x := c.store.x + 1 }
  | 6 => { c with pc := 3 }
  | 7 => if c.store.x = 0 then { c with pc := 10 }
         else { c with pc := 8, store.x := c.store.x - 1 }
  | 8 => { c with pc := 9, store.h := c.store.h + 1 }
  | 9 => { c with pc := 7 }
  | _ => c

/-- Exactly `n` executions of the displayed primitive transition function. -/
inductive Steps : Nat → Config Frame → Config Frame → Prop
  | refl (c) : Steps 0 c c
  | cons : Steps n (step a) b → Steps (n + 1) a b

theorem Steps.trans (ab : Steps n a b) (bc : Steps m b c) : Steps (n + m) a c := by
  induction ab with
  | refl => simpa using bc
  | cons h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons (ih bc)

/-- Drain T into X without changing H or the frame. -/
theorem drain_t (t h x : Nat) (f : Frame) :
    Steps (3 * t + 1) ⟨0, ⟨t, h, x, f⟩⟩ ⟨3, ⟨0, h, x + t, f⟩⟩ := by
  induction t generalizing x with
  | zero => simpa [step] using Steps.cons (Steps.refl (⟨3, ⟨0, h, x, f⟩⟩ : Config Frame))
  | succ t ih =>
    have q : Steps (3 * t + 1 + 1 + 1 + 1)
        ⟨0, ⟨t + 1, h, x, f⟩⟩ ⟨3, ⟨0, h, x + 1 + t, f⟩⟩ := by
      apply Steps.cons; apply Steps.cons; apply Steps.cons
      simpa [step] using ih (x + 1)
    have hn : 3 * (t + 1) + 1 = 3 * t + 1 + 1 + 1 + 1 := by omega
    rw [hn]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using q

/-- Drain H into both T and X. -/
theorem drain_h (h t x : Nat) (f : Frame) :
    Steps (4 * h + 1) ⟨3, ⟨t, h, x, f⟩⟩ ⟨7, ⟨t + h, 0, x + h, f⟩⟩ := by
  induction h generalizing t x with
  | zero => simpa [step] using Steps.cons (Steps.refl (⟨7, ⟨t, 0, x, f⟩⟩ : Config Frame))
  | succ h ih =>
    have q : Steps (4 * h + 1 + 1 + 1 + 1 + 1)
        ⟨3, ⟨t, h + 1, x, f⟩⟩ ⟨7, ⟨t + 1 + h, 0, x + 1 + h, f⟩⟩ := by
      apply Steps.cons; apply Steps.cons; apply Steps.cons; apply Steps.cons
      simpa [step] using ih (t + 1) (x + 1)
    have hn : 4 * (h + 1) + 1 = 4 * h + 1 + 1 + 1 + 1 + 1 := by omega
    rw [hn]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using q

/-- Restore X into H without changing T or the frame. -/
theorem restore_x (x t h : Nat) (f : Frame) :
    Steps (3 * x + 1) ⟨7, ⟨t, h, x, f⟩⟩ ⟨10, ⟨t, h + x, 0, f⟩⟩ := by
  induction x generalizing h with
  | zero => simpa [step] using Steps.cons (Steps.refl (⟨10, ⟨t, h, 0, f⟩⟩ : Config Frame))
  | succ x ih =>
    have q : Steps (3 * x + 1 + 1 + 1 + 1)
        ⟨7, ⟨t, h, x + 1, f⟩⟩ ⟨10, ⟨t, h + 1 + x, 0, f⟩⟩ := by
      apply Steps.cons; apply Steps.cons; apply Steps.cons
      simpa [step] using ih (h + 1)
    have hn : 3 * (x + 1) + 1 = 3 * x + 1 + 1 + 1 + 1 := by omega
    rw [hn]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using q

/-- Exact S36 pre-guard effect and number of primitive visits. -/
theorem pre_guard (t h : Nat) (f : Frame) :
    Steps (6 * t + 7 * h + 3)
      ⟨0, ⟨t, h, 0, f⟩⟩ ⟨10, ⟨h, t + h, 0, f⟩⟩ := by
  have a := drain_t t h 0 f
  have b := drain_h h 0 t f
  have c := restore_x (t + h) h 0 f
  simp only [Nat.zero_add] at a b c
  have q := a.trans (b.trans c)
  have hn : 6 * t + 7 * h + 3 = 3 * t + 1 + (4 * h + 1 + (3 * (t + h) + 1)) := by omega
  rw [hn]
  exact q

/-- A sum-one guard supplies an incoming falsity witness, not a new theorem
about a temporary sum. -/
theorem sum_one_incoming {t h : Nat} (guard : t + h = 1) : t = 1 ∨ h = 1 := by
  omega

theorem sum_one_proved {Proved : Nat → Prop} {t h : Nat}
    (ht : Proved t) (hh : Proved h) (guard : t + h = 1) : Proved 1 := by
  rcases sum_one_incoming guard with ht1 | hh1
  · simpa [ht1] using ht
  · simpa [hh1] using hh

end M6.Source.S36Drain

#print axioms M6.Source.S36Drain.pre_guard
#print axioms M6.Source.S36Drain.sum_one_proved

