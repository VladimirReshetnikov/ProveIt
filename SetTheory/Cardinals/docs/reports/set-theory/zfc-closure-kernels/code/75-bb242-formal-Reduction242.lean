import Tables242
import BlockSimulation
set_option autoImplicit false
namespace BranchBorrow242
open PositiveBlocks

structure Config where
  state : Nat
  head : Int
  tape : Int → Bool

def write (t : Int → Bool) (h : Int) (b : Bool) : Int → Bool :=
  fun x => if x = h then b else t x

def step (rows : Nat → Bool → Option Action) (c : Config) : Config :=
  match rows c.state (c.tape c.head) with
  | none => c
  | some a => ⟨a.next, if a.right then c.head + 1 else c.head - 1,
      write c.tape c.head a.write⟩

def terminal (c : Config) : Prop := c.state = 254

def Inv (c : Config) : Prop :=
  ((c.state = 18 ∨ c.state = 47 ∨ c.state = 65) →
    c.tape (c.head - 1) = false) ∧
  (c.state = 27 → c.tape c.head = false)

def Checkpoint (c : Config) : Prop := Inv c ∧ c.state ≠ 15

theorem write_read (t : Int → Bool) (h : Int) : write t h (t h) = t := by
  funext x
  by_cases hx : x = h
  · simp [write, hx]
  · simp [write, hx]

theorem write_eq (t : Int → Bool) (h : Int) (b : Bool) (hb : t h = b) :
    write t h b = t := by rw [← hb]; exact write_read t h

theorem step_known (rows : Nat → Bool → Option Action) (c : Config)
    (q : Nat) (b dir : Bool) (target : Nat)
    (hq : c.state = q) (hb : c.tape c.head = b)
    (hr : rows q b = some ⟨b, dir, target⟩) :
    step rows c = {c with state := target, head := (if dir then c.head + 1 else c.head - 1)} := by
  simp only [step, hq, hb, hr]
  rw [write_eq c.tape c.head b hb]

theorem old_terminal_fixed (c : Config) (hc : terminal c) : step oldRow c = c := by
  simp [terminal] at hc
  simp [step, hc, old_halt]

theorem new_terminal_fixed (c : Config) (hc : terminal c) : step newRow c = c := by
  simp [terminal] at hc
  simp [step, hc, new_halt]

theorem invariant_step (c : Config) (hc : Inv c) : Inv (step oldRow c) := by
  cases hr : oldRow c.state (c.tape c.head) with
  | none => simpa [step, hr] using hc
  | some a =>
      have facts := incoming_all c.state (c.tape c.head) a hr
      constructor
      · intro h
        have hn : a.next = 18 ∨ a.next = 47 ∨ a.next = 65 := by
          simpa [step, hr] using h
        obtain ⟨hd, hw⟩ := facts.1 hn
        simp [step, hr, hd, hw, write]
      · intro h
        have hn : a.next = 27 := by simpa [step, hr] using h
        obtain ⟨hq, _, hd⟩ := facts.2.1 hn
        have hz := hc.1 hq
        have he : c.head - 1 ≠ c.head := by omega
        simpa [step, hr, hd, write, he] using hz

theorem invariant_run (n : Nat) (c : Config) (hc : Inv c) :
    Inv (run (step oldRow) n c) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact invariant_step _ ih

theorem ordinary_rows (c : Config) (hc : Checkpoint c)
    (he : ¬ (c.state = 11 ∧ c.tape c.head = false)) :
    newRow c.state (c.tape c.head) = oldRow c.state (c.tape c.head) := by
  have h27 : ¬ (c.state = 27 ∧ c.tape c.head = true) := by
    rintro ⟨hq, hb⟩
    have hz := hc.1.2 hq
    simp [hb] at hz
  rw [newRow_patch]
  simp [patched, hc.2, he, h27]

theorem ordinary_step (c : Config) (hc : Checkpoint c)
    (he : ¬ (c.state = 11 ∧ c.tape c.head = false)) :
    step newRow c = step oldRow c := by
  unfold step
  rw [ordinary_rows c hc he]

theorem ordinary_checkpoint (c : Config) (hc : Checkpoint c)
    (he : ¬ (c.state = 11 ∧ c.tape c.head = false)) :
    Checkpoint (step oldRow c) := by
  refine ⟨invariant_step c hc.1, ?_⟩
  cases hr : oldRow c.state (c.tape c.head) with
  | none => simpa [step, hr] using hc.2
  | some a =>
      intro hn
      have ha : a.next = 15 := by simpa [step, hr] using hn
      exact he ((incoming_all c.state (c.tape c.head) a hr).2.2 ha)

-- Literal finite rows used by the two exceptional blocks.
theorem old11 : oldRow 11 false = some ⟨false, true, 15⟩ := rfl
theorem old15_false : oldRow 15 false = some ⟨false, true, 21⟩ := rfl
theorem old15_true : oldRow 15 true = some ⟨true, true, 22⟩ := rfl
theorem new11 : newRow 11 false = some ⟨false, true, 27⟩ := rfl
theorem new27_false : newRow 27 false = some ⟨false, false, 32⟩ := rfl
theorem new27_true : newRow 27 true = some ⟨true, true, 22⟩ := rfl
theorem new32 : newRow 32 false = some ⟨false, true, 45⟩ := rfl
theorem new45 : newRow 45 false = some ⟨false, true, 21⟩ := rfl

theorem exceptional_zero (c : Config) (hq : c.state = 11)
    (h0 : c.tape c.head = false) (h1 : c.tape (c.head + 1) = false) :
    run (step oldRow) 2 c = {c with state := 21, head := c.head + 2} ∧
    run (step newRow) 4 c = {c with state := 21, head := c.head + 2} := by
  have o1 := step_known oldRow c 11 false true 15 hq h0 old11
  have o2 := step_known oldRow {c with state := 15, head := c.head + 1}
    15 false true 21 rfl h1 old15_false
  have n1 := step_known newRow c 11 false true 27 hq h0 new11
  have n2 := step_known newRow {c with state := 27, head := c.head + 1}
    27 false false 32 rfl h1 new27_false
  have n3 := step_known newRow {c with state := 32}
    32 false true 45 rfl h0 new32
  have n4 := step_known newRow {c with state := 45, head := c.head + 1}
    45 false true 21 rfl h1 new45
  have n2' : step newRow {c with state := 27, head := c.head + 1} =
      {c with state := 32} := by simpa using n2
  constructor
  · simp [run, o1, o2, Int.add_assoc]
  · simp [run, n1, n2', n3, n4, Int.add_assoc]

theorem exceptional_one (c : Config) (hq : c.state = 11)
    (h0 : c.tape c.head = false) (h1 : c.tape (c.head + 1) = true) :
    run (step oldRow) 2 c = {c with state := 22, head := c.head + 2} ∧
    run (step newRow) 2 c = {c with state := 22, head := c.head + 2} := by
  have o1 := step_known oldRow c 11 false true 15 hq h0 old11
  have o2 := step_known oldRow {c with state := 15, head := c.head + 1}
    15 true true 22 rfl h1 old15_true
  have n1 := step_known newRow c 11 false true 27 hq h0 new11
  have n2 := step_known newRow {c with state := 27, head := c.head + 1}
    27 true true 22 rfl h1 new27_true
  constructor
  · simp [run, o1, o2, Int.add_assoc]
  · simp [run, n1, n2, Int.add_assoc]

theorem matching_blocks (c : Config) (hc : Checkpoint c) :
    ∃ k l d, 0 < k ∧ 0 < l ∧ run (step oldRow) k c = d ∧
      run (step newRow) l c = d ∧ Checkpoint d := by
  by_cases he : c.state = 11 ∧ c.tape c.head = false
  · cases hb : c.tape (c.head + 1) with
    | false =>
        obtain ⟨ho, hn⟩ := exceptional_zero c he.1 he.2 hb
        refine ⟨2, 4, {c with state := 21, head := c.head + 2}, by decide,
          by decide, ho, hn, ?_⟩
        constructor
        · rw [← ho]; exact invariant_run 2 c hc.1
        · simp
    | true =>
        obtain ⟨ho, hn⟩ := exceptional_one c he.1 he.2 hb
        refine ⟨2, 2, {c with state := 22, head := c.head + 2}, by decide,
          by decide, ho, hn, ?_⟩
        constructor
        · rw [← ho]; exact invariant_run 2 c hc.1
        · simp
  · refine ⟨1, 1, step oldRow c, by decide, by decide, rfl, ?_,
      ordinary_checkpoint c hc he⟩
    exact ordinary_step c hc he

theorem checkpoint_halting_iff (c : Config) (hc : Checkpoint c) :
    Halts (step oldRow) terminal c ↔ Halts (step newRow) terminal c := by
  exact PositiveBlocks.halting_iff _ _ _ old_terminal_fixed new_terminal_fixed
    Checkpoint matching_blocks c hc

theorem start95_halting_iff (head : Int) (tape : Int → Bool) :
    Halts (step oldRow) terminal ⟨95, head, tape⟩ ↔
    Halts (step newRow) terminal ⟨95, head, tape⟩ := by
  apply checkpoint_halting_iff
  simp [Checkpoint, Inv]

theorem blank_halting_iff :
    Halts (step oldRow) terminal ⟨95, 0, fun _ => false⟩ ↔
    Halts (step newRow) terminal ⟨95, 0, fun _ => false⟩ :=
  start95_halting_iff 0 (fun _ => false)

theorem blank_nonhalting_iff :
    ¬ Halts (step oldRow) terminal ⟨95, 0, fun _ => false⟩ ↔
    ¬ Halts (step newRow) terminal ⟨95, 0, fun _ => false⟩ :=
  not_congr blank_halting_iff

theorem calibration_transfer (C : Prop)
    (old_calibration : (¬ Halts (step oldRow) terminal ⟨95, 0, fun _ => false⟩) ↔ C) :
    (¬ Halts (step newRow) terminal ⟨95, 0, fun _ => false⟩) ↔ C :=
  blank_nonhalting_iff.symm.trans old_calibration

end BranchBorrow242
