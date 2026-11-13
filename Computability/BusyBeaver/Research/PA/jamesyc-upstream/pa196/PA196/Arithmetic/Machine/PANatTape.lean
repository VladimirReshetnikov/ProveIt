module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PATape
@[expose] public section

/-! Two natural-number stacks represent a finite binary tape relative to its
head. This representation connects arithmetic data with the independently
defined bi-infinite tape, without changing the literal machine. -/

namespace PA196.Arithmetic.Machine.PA.NatTape
open M6

def push (b : Bool) (n : Nat) : Nat := 2 * n + b.toNat

@[simp] theorem push_head (b : Bool) (n : Nat) : (push b n).testBit 0 = b := by
  cases b <;> simp [push, Nat.testBit_eq_decide_div_mod_eq, Nat.add_mod]

@[simp] theorem push_div (b : Bool) (n : Nat) : push b n / 2 = n := by
  cases b <;> simp [push] <;> omega

@[simp] theorem push_bit_succ (b : Bool) (n i : Nat) :
    (push b n).testBit (i + 1) = n.testBit i := by
  rw [Nat.testBit_add_one, push_div]

/-- Equality at every cell, including the arbitrary absolute head position. -/
def Represents (left right : Nat) (t : Tape) (h : Int) : Prop :=
  (∀ i : Nat, t (h + i) = right.testBit i) ∧
  (∀ i : Nat, t (h - (i + 1)) = left.testBit i)

theorem represents_blank : Represents 0 0 (fun _ => false) 0 := by
  constructor <;> intro i <;> simp

theorem represents_read {left right : Nat} {t : Tape} {h : Int}
    (hr : Represents left right t h) : t h = right.testBit 0 := by
  simpa using hr.1 0

theorem represents_move_right {left right : Nat} {t : Tape} {h : Int}
    (hr : Represents left right t h) (w : Bool) :
    Represents (push w left) (right / 2) (writeTape t h w) (h + 1) := by
  constructor
  · intro i
    have hn : h + 1 + (i : Int) ≠ h := by omega
    have he : h + 1 + (i : Int) = h + ((i + 1 : Nat) : Int) := by omega
    simp only [writeTape, hn, ite_false]
    rw [he, hr.1, Nat.testBit_div_two]
  · intro i
    cases i with
    | zero => rw [push_head]; simp [writeTape]
    | succ i =>
      rw [push_bit_succ]
      have he : h + 1 - ((i : Int) + 1 + 1) = h - ((i : Int) + 1) := by omega
      have hn : h - ((i : Int) + 1) ≠ h := by omega
      simpa only [Int.natCast_add, Int.natCast_one, he, writeTape, hn, ite_false]
        using hr.2 i

theorem represents_move_left {left right : Nat} {t : Tape} {h : Int}
    (hr : Represents left right t h) (w : Bool) :
    Represents (left / 2) (push (left.testBit 0) (push w (right / 2)))
      (writeTape t h w) (h - 1) := by
  constructor
  · intro i
    cases i with
    | zero =>
      rw [push_head]
      have hn : h - 1 ≠ h := by omega
      simpa [writeTape, hn] using hr.2 0
    | succ i =>
      rw [push_bit_succ]
      cases i with
      | zero => rw [push_head]; simp [writeTape]
      | succ i =>
        rw [push_bit_succ, Nat.testBit_div_two]
        have he : h - 1 + ((i : Int) + 1 + 1) = h + ((i : Int) + 1) := by omega
        have hn : h + ((i : Int) + 1) ≠ h := by omega
        simpa only [Int.natCast_add, Int.natCast_one, he, writeTape, hn, ite_false]
          using hr.1 (i + 1)
  · intro i
    rw [Nat.testBit_div_two]
    have he : h - 1 - ((i : Int) + 1) = h - ((i : Int) + 1 + 1) := by omega
    have hn : h - ((i : Int) + 1 + 1) ≠ h := by omega
    simpa only [Int.natCast_add, Int.natCast_one, he, writeTape, hn, ite_false]
      using hr.2 (i + 1)

structure Configuration where
  control : Control
  left : Nat
  right : Nat
  deriving DecidableEq

def advance (a : Action) (c : Configuration) : Configuration :=
  if a.right then
    ⟨a.next, push a.write c.left, c.right / 2⟩
  else
    ⟨a.next, c.left / 2, push (c.left.testBit 0) (push a.write (c.right / 2))⟩

def step (c : Configuration) : Option Configuration :=
  c.control.map fun q => advance (row q (c.right.testBit 0)) c

def Rel (s : Configuration) (c : PA196.Arithmetic.Machine.Configuration) : Prop :=
  s.control = c.control ∧ Represents s.left s.right c.tape c.head

def blank : Configuration := ⟨start, 0, 0⟩

theorem blank_rel : Rel blank PA196.Arithmetic.Machine.blank := ⟨rfl, represents_blank⟩

theorem advance_represents (s : Configuration) {t : Tape} {h : Int}
    (hr : Represents s.left s.right t h) (a : Action) :
    Represents (advance a s).left (advance a s).right (writeTape t h a.write)
      (h + (if a.right then 1 else -1)) := by
  cases ha : a.right
  · simpa [advance, ha, Int.sub_eq_add_neg] using represents_move_left hr a.write
  · simpa [advance, ha] using represents_move_right hr a.write

theorem step_simulates {s s' : Configuration} {c : PA196.Arithmetic.Machine.Configuration}
    (hr : Rel s c) (hs : step s = some s') :
    ∃ c', PA196.Arithmetic.Machine.step c = some c' ∧ Rel s' c' := by
  cases hq : s.control with
  | none => simp [step, hq] at hs
  | some q =>
    simp only [step, hq, Option.map_some, Option.some.injEq] at hs
    subst s'
    let a := row q (s.right.testBit 0)
    refine ⟨⟨a.next, c.head + (if a.right then 1 else -1),
      writeTape c.tape c.head a.write⟩, ?_, ?_⟩
    · simp [PA196.Arithmetic.Machine.step, ← hr.1, hq, represents_read hr.2, a]
    · constructor
      · simp [advance, a]; split <;> rfl
      · exact advance_represents s hr.2 a

theorem step_reflects {s : Configuration} {c c' : PA196.Arithmetic.Machine.Configuration}
    (hr : Rel s c) (hc : PA196.Arithmetic.Machine.step c = some c') :
    ∃ s', step s = some s' ∧ Rel s' c' := by
  cases hq : s.control with
  | none => simp [PA196.Arithmetic.Machine.step, ← hr.1, hq] at hc
  | some q =>
    let s' := advance (row q (s.right.testBit 0)) s
    have hs : step s = some s' := by simp [step, hq, s']
    obtain ⟨c'', he, hr'⟩ := step_simulates hr hs
    have hc' : c'' = c' := Option.some.inj (he.symm.trans hc)
    exact ⟨s', hs, hc' ▸ hr'⟩

def run : Nat → Configuration → Option Configuration
  | 0, s => some s
  | n + 1, s => (step s).bind (run n)

def Halts (s : Configuration) : Prop :=
  ∃ n s', run n s = some s' ∧ s'.control = halt

theorem run_simulates {s s' : Configuration} {c : PA196.Arithmetic.Machine.Configuration}
    (n : Nat) (hr : Rel s c) (hs : run n s = some s') :
    ∃ c', PA196.Arithmetic.Machine.run n c = some c' ∧ Rel s' c' := by
  induction n generalizing s c with
  | zero =>
    simp only [run, Option.some.injEq] at hs
    subst s'
    exact ⟨c, rfl, hr⟩
  | succ n ih =>
    cases hstep : step s with
    | none => simp [run, hstep] at hs
    | some s1 =>
      have hs1 : run n s1 = some s' := by simpa [run, hstep] using hs
      obtain ⟨c1, hc1, hr1⟩ := step_simulates hr hstep
      obtain ⟨c', hc', hr'⟩ := ih hr1 hs1
      exact ⟨c', by simpa [PA196.Arithmetic.Machine.run, hc1] using hc', hr'⟩

theorem run_reflects {s : Configuration} {c c' : PA196.Arithmetic.Machine.Configuration}
    (n : Nat) (hr : Rel s c) (hc : PA196.Arithmetic.Machine.run n c = some c') :
    ∃ s', run n s = some s' ∧ Rel s' c' := by
  induction n generalizing s c with
  | zero =>
    simp only [PA196.Arithmetic.Machine.run, Option.some.injEq] at hc
    subst c'
    exact ⟨s, rfl, hr⟩
  | succ n ih =>
    cases hstep : PA196.Arithmetic.Machine.step c with
    | none => simp [PA196.Arithmetic.Machine.run, hstep] at hc
    | some c1 =>
      have hc1 : PA196.Arithmetic.Machine.run n c1 = some c' := by simpa [PA196.Arithmetic.Machine.run, hstep] using hc
      obtain ⟨s1, hs1, hr1⟩ := step_reflects hr hstep
      obtain ⟨s', hs', hr'⟩ := ih hr1 hc1
      exact ⟨s', by simpa [run, hs1] using hs', hr'⟩

theorem halts_iff {s : Configuration} {c : PA196.Arithmetic.Machine.Configuration}
    (hr : Rel s c) : Halts s ↔ PA196.Arithmetic.Machine.Halts c := by
  constructor
  · rintro ⟨n, s', hs', hh⟩
    obtain ⟨c', hc', hr'⟩ := run_simulates n hr hs'
    exact ⟨n, c', hc', hr'.1.symm.trans hh⟩
  · rintro ⟨n, c', hc', hh⟩
    obtain ⟨s', hs', hr'⟩ := run_reflects n hr hc'
    exact ⟨n, s', hs', hr'.1.trans hh⟩

theorem blank_halts_iff : Halts blank ↔ PA196.Arithmetic.Machine.Halts PA196.Arithmetic.Machine.blank :=
  halts_iff blank_rel

#print axioms represents_move_right
#print axioms represents_move_left
#print axioms step_simulates
#print axioms blank_halts_iff

end PA196.Arithmetic.Machine.PA.NatTape

