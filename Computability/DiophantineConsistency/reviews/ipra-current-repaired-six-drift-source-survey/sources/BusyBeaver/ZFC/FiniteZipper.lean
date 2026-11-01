import Lean.Elab.Tactic.Omega
import BusyBeaver.Core

/-!
Finite zero-exterior tape zippers, related to the existing Core semantics.
A representation gives the state, absolute head and every tape read on both
half-lines. One-step and balanced-block soundness hold for every table.
This is a computation interface, not a compiler or consistency calibration.
-/
namespace SetTheory.BusyBeaver.ZFC.FiniteZipper
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Finite zipper with exterior zeros; left lists nearest cells first and
right starts at the head. The head coordinate is retained explicitly. -/
structure ZipConfig (states : Nat) where
  state : Option (Fin states)
  head : Int
  left : List Bool
  right : List Bool
  deriving DecidableEq, Repr

/-- Every tape cell on both half-lines is specified, including the blank exterior. -/
def ZipRep {n : Nat} (c : Config n) (z : ZipConfig n) : Prop :=
  c.state = z.state ∧ c.head = z.head ∧
  (∀ i : Nat, Tape.read c.tape (z.head - ((i + 1 : Nat) : Int)) = z.left.getD i false) ∧
  (∀ i : Nat, Tape.read c.tape (z.head + (i : Int)) = z.right.getD i false)

private theorem getD_tail (l : List Bool) (i : Nat) :
    l.tail.getD i false = l.getD (i + 1) false := by
  cases l <;> rfl

private theorem getD_cons_zero (b : Bool) (l : List Bool) :
    (b :: l).getD 0 false = b := rfl

private theorem getD_cons_succ (b : Bool) (l : List Bool) (i : Nat) :
    (b :: l).getD (i + 1) false = l.getD i false := rfl

def zipWrite {n : Nat} (z : ZipConfig n) (b : Bool) : ZipConfig n :=
  { z with right := b :: z.right.tail }

def zipRight {n : Nat} (z : ZipConfig n) : ZipConfig n :=
  { z with head := z.head + 1,
           left := z.right.getD 0 false :: z.left, right := z.right.tail }

def zipLeft {n : Nat} (z : ZipConfig n) : ZipConfig n :=
  { z with head := z.head - 1,
           left := z.left.tail, right := z.left.getD 0 false :: z.right }

private theorem zipRep_write {n : Nat} {c : Config n} {z : ZipConfig n}
    (h : ZipRep c z) (b : Bool) :
    ZipRep { c with tape := Tape.write c.tape c.head b } (zipWrite z b) := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro i
    change Tape.read (Tape.write c.tape c.head b) (z.head - ((i + 1 : Nat) : Int)) = z.left.getD i false
    have hn : z.head - ((i + 1 : Nat) : Int) ≠ c.head := by
      rw [h.2.1]
      omega
    rw [Tape.read_write_of_ne c.tape hn b]
    exact h.2.2.1 i
  · intro i
    cases i with
    | zero =>
      change Tape.read (Tape.write c.tape c.head b) (z.head + 0) = b
      simp [h.2.1]
    | succ i =>
      change Tape.read (Tape.write c.tape c.head b) (z.head + ((i + 1 : Nat) : Int)) =
        z.right.tail.getD i false
      rw [Tape.read_write_of_ne c.tape (by rw [h.2.1]; omega) b, getD_tail]
      exact h.2.2.2 (i + 1)

private theorem zipRep_right {n : Nat} {c : Config n} {z : ZipConfig n}
    (h : ZipRep c z) :
    ZipRep { c with head := c.head + 1 } (zipRight z) := by
  refine ⟨h.1, by simp only [zipRight, h.2.1], ?_, ?_⟩
  · intro i
    cases i with
    | zero =>
      change Tape.read c.tape (z.head + 1 - 1) = z.right.getD 0 false
      simpa using h.2.2.2 0
    | succ i =>
      change Tape.read c.tape (z.head + 1 - ((i + 1 + 1 : Nat) : Int)) = z.left.getD i false
      have e : z.head + 1 - ((i + 1 + 1 : Nat) : Int) = z.head - ((i + 1 : Nat) : Int) := by omega
      rw [e]
      exact h.2.2.1 i
  · intro i
    change Tape.read c.tape (z.head + 1 + (i : Int)) = z.right.tail.getD i false
    rw [getD_tail]
    have e : z.head + 1 + (i : Int) = z.head + ((i + 1 : Nat) : Int) := by omega
    rw [e]
    exact h.2.2.2 (i + 1)

private theorem zipRep_left {n : Nat} {c : Config n} {z : ZipConfig n}
    (h : ZipRep c z) :
    ZipRep { c with head := c.head - 1 } (zipLeft z) := by
  refine ⟨h.1, by simp only [zipLeft, h.2.1], ?_, ?_⟩
  · intro i
    change Tape.read c.tape (z.head - 1 - ((i + 1 : Nat) : Int)) = z.left.tail.getD i false
    rw [getD_tail]
    have e : z.head - 1 - ((i + 1 : Nat) : Int) = z.head - ((i + 1 + 1 : Nat) : Int) := by omega
    rw [e]
    exact h.2.2.1 (i + 1)
  · intro i
    cases i with
    | zero =>
      change Tape.read c.tape (z.head - 1 + 0) = z.left.getD 0 false
      simpa using h.2.2.1 0
    | succ i =>
      change Tape.read c.tape (z.head - 1 + ((i + 1 : Nat) : Int)) = z.right.getD i false
      have e : z.head - 1 + ((i + 1 : Nat) : Int) = z.head + (i : Int) := by omega
      rw [e]
      exact h.2.2.2 i

private theorem zipRep_state {n : Nat} {c : Config n} {z : ZipConfig n}
    (h : ZipRep c z) (state : Option (Fin n)) :
    ZipRep { c with state := state } { z with state := state } :=
  ⟨rfl, h.2⟩

def zipStep {n : Nat} (M : Machine n) (z : ZipConfig n) : ZipConfig n :=
  match z.state with
  | none => z
  | some q =>
    let a := M.transition q (z.right.getD 0 false)
    let written := zipWrite z a.write
    let moved := match a.move with
      | .left => zipLeft written
      | .right => zipRight written
    { moved with state := a.next }

/-- One finite zipper transition represents the existing Core transition,
for any table and every finite-support tape; this is not a new machine semantics. -/
theorem zipStep_sound {n : Nat} (M : Machine n) {c : Config n} {z : ZipConfig n}
    (h : ZipRep c z) : ZipRep (M.step c) (zipStep M z) := by
  cases hz : z.state with
  | none =>
    have hc : c.state = none := h.1.trans hz
    simpa only [Machine.step, hc, zipStep, hz] using h
  | some q =>
    have hc : c.state = some q := h.1.trans hz
    have hr : Tape.read c.tape c.head = z.right.getD 0 false := by
      rw [h.2.1]
      simpa using h.2.2.2 0
    let a := M.transition q (z.right.getD 0 false)
    have hw := zipRep_write h a.write
    cases hm : a.move with
    | left =>
      have hh := zipRep_state (zipRep_left hw) a.next
      simp only [a] at hm
      simpa only [Machine.step, hc, hr, zipStep, hz, a, hm, Move.apply,
        zipWrite, zipLeft] using hh
    | right =>
      have hh := zipRep_state (zipRep_right hw) a.next
      simp only [a] at hm
      simpa only [Machine.step, hc, hr, zipStep, hz, a, hm, Move.apply,
        zipWrite, zipRight] using hh

/-- A balanced 2^depth-step checker avoids a linear-depth reduction stack. -/
def zipBlock {n : Nat} (M : Machine n) : Nat → ZipConfig n → ZipConfig n
  | 0, z => zipStep M z
  | depth + 1, z => zipBlock M depth (zipBlock M depth z)

theorem zipBlock_sound {n : Nat} (M : Machine n) (depth : Nat)
    {c : Config n} {z : ZipConfig n} (h : ZipRep c z) :
    ZipRep (M.runFrom c (2 ^ depth)) (zipBlock M depth z) := by
  induction depth generalizing c z with
  | zero => exact zipStep_sound M h
  | succ depth ih =>
    have first := ih h
    have second := ih first
    have twice : 2 ^ (depth + 1) = 2 ^ depth + 2 ^ depth := by
      rw [Nat.pow_succ]
      omega
    rw [twice, Machine.runFrom_add]
    exact second

/-- Read a finite zipper at any integer position, with zero exterior. -/
def frameRead {n : Nat} (z : ZipConfig n) (pos : Int) : Bool :=
  if pos < z.head then
    z.left.getD (z.head - pos - 1).toNat false
  else
    z.right.getD (pos - z.head).toNat false

theorem read_eq_frameRead {n : Nat} {c : Config n} {z : ZipConfig n}
    (h : ZipRep c z) (pos : Int) : Tape.read c.tape pos = frameRead z pos := by
  unfold frameRead
  split
  · rename_i hpos
    have hn : 0 ≤ z.head - pos - 1 := by omega
    have hi : ((z.head - pos - 1).toNat : Int) = z.head - pos - 1 :=
      Int.toNat_of_nonneg hn
    have e : pos = z.head - (((z.head - pos - 1).toNat + 1 : Nat) : Int) := by omega
    calc
      Tape.read c.tape pos = Tape.read c.tape
          (z.head - (((z.head - pos - 1).toNat + 1 : Nat) : Int)) :=
        congrArg (Tape.read c.tape) e
      _ = z.left.getD (z.head - pos - 1).toNat false := h.2.2.1 _
  · rename_i hpos
    have hn : 0 ≤ pos - z.head := by omega
    have hi : ((pos - z.head).toNat : Int) = pos - z.head := Int.toNat_of_nonneg hn
    have e : pos = z.head + ((pos - z.head).toNat : Int) := by omega
    calc
      Tape.read c.tape pos = Tape.read c.tape
          (z.head + ((pos - z.head).toNat : Int)) := congrArg (Tape.read c.tape) e
      _ = z.right.getD (pos - z.head).toNat false := h.2.2.2 _

/-- Activity at an endpoint excludes an earlier halt, because Core's terminal
configuration is stationary. This makes no claim about first dispatch arrival. -/
theorem active_through_of_endpoint {n : Nat} (M : Machine n) (last : Nat)
    (hLast : (M.run last).state ≠ none) :
    ∀ elapsed, elapsed ≤ last → (M.run elapsed).state ≠ none := by
  intro elapsed hBound hHalted
  have hSum : elapsed + (last - elapsed) = last := by omega
  have hRun : M.run last = M.run elapsed := by
    calc
      M.run last = M.run (elapsed + (last - elapsed)) := by rw [hSum]
      _ = M.runFrom (M.run elapsed) (last - elapsed) := M.run_add_eq_runFrom _ _
      _ = M.run elapsed := M.runFrom_of_halted _ hHalted _
  apply hLast
  rw [hRun]
  exact hHalted


#print axioms zipStep_sound
#print axioms zipBlock_sound
#print axioms read_eq_frameRead
#print axioms active_through_of_endpoint
end SetTheory.BusyBeaver.ZFC.FiniteZipper
