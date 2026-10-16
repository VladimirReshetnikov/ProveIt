import BusyBeaver.ZFC.Table252

/-!
First local compiler-verification layer for the frozen public Wade backend.

The engine uses a movable double-zero selector and unary register blocks.
This is the engine of Table252, not Mira-Cult's single-marker interpreter.
The theorems below execute actual literal rows of machine252 on an arbitrary
finite-support tape. They prove an increment scan and its unary-register effect;
they do not assume an abstract register-machine simulation to obtain that effect.

The return-PC excursion, selector relocation, decrement, dispatcher, bootstrap,
whole enumerator, and consistency calibration remain separate proof obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.WadeMachine

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev Literal := machine252

/-- Named public-backend entry points in the frozen canonical numbering. -/
def inc : Fin 252 := ⟨13, by decide⟩
def incGap : Fin 252 := ⟨14, by decide⟩
def incOnes : Fin 252 := ⟨15, by decide⟩
def incSeparator : Fin 252 := ⟨16, by decide⟩
def retOne : Fin 252 := ⟨23, by decide⟩
def retOneProbe : Fin 252 := ⟨24, by decide⟩
def retOneMarker : Fin 252 := ⟨25, by decide⟩
def retTwo : Fin 252 := ⟨26, by decide⟩
def root : Fin 252 := ⟨54, by decide⟩
def breakZero : Fin 252 := ⟨55, by decide⟩

/-- A live configuration; no quotient or alternative tape semantics is used. -/
def atState {n : Nat} (q : Fin n) (head : Int) (tape : Tape) : Config n :=
  { state := some q, head := head, tape := tape }

/-- Finite actual execution, with its step count hidden only for composition. -/
def Reaches {n : Nat} (M : Machine n) (c d : Config n) : Prop :=
  ∃ steps, M.runFrom c steps = d

theorem reaches_refl {n : Nat} (M : Machine n) (c : Config n) : Reaches M c c :=
  ⟨0, rfl⟩

theorem reaches_trans {n : Nat} {M : Machine n} {c d e : Config n}
    (hcd : Reaches M c d) (hde : Reaches M d e) : Reaches M c e := by
  obtain ⟨i, hi⟩ := hcd
  obtain ⟨j, hj⟩ := hde
  refine ⟨i + j, ?_⟩
  rw [Machine.runFrom_add, hi, hj]

theorem reaches_step {n : Nat} {M : Machine n} {c d : Config n}
    (h : M.step c = d) : Reaches M c d := by
  exact ⟨1, by simpa only [Machine.runFrom] using h⟩

/-- A finite constant-bit interval, with all other tape cells unconstrained. -/
def Span (tape : Tape) (head : Int) (bit : Bool) (length : Nat) : Prop :=
  ∀ i : Nat, i < length → Tape.read tape (head + (i : Int)) = bit

theorem span_tail {tape : Tape} {head : Int} {bit : Bool} {length : Nat}
    (h : Span tape head bit (length + 1)) : Span tape (head + 1) bit length := by
  intro i hi
  have hp : (head + 1) + (i : Int) = head + ((i + 1 : Nat) : Int) := by omega
  rw [hp]
  exact h (i + 1) (by omega)

theorem span_write_left {tape : Tape} {head pos : Int} {bit written : Bool}
    {length : Nat} (h : Span tape head bit length) (hp : pos < head) :
    Span (Tape.write tape pos written) head bit length := by
  intro i hi
  rw [Tape.read_write_of_ne tape (by omega : head + (i : Int) ≠ pos) written]
  exact h i hi

theorem step_writing {n : Nat} (M : Machine n) (q q' : Fin n)
    (head : Int) (tape : Tape) (read written : Bool) (move : Move)
    (hr : Tape.read tape head = read)
    (ht : M.transition q read = { write := written, move := move, next := some q' }) :
    M.step (atState q head tape) =
      atState q' (move.apply head) (Tape.write tape head written) := by
  simp only [Machine.step, atState, hr, ht]

theorem step_preserving {n : Nat} (M : Machine n) (q q' : Fin n)
    (head : Int) (tape : Tape) (bit : Bool) (move : Move)
    (hr : Tape.read tape head = bit)
    (ht : M.transition q bit = { write := bit, move := move, next := some q' }) :
    M.step (atState q head tape) = atState q' (move.apply head) tape := by
  have hw : Tape.write tape head bit = tape := by
    rw [← hr]
    exact Tape.write_read_self tape head
  rw [step_writing M q q' head tape bit bit move hr ht, hw]

/-- A genuine frame-preserving scan in Core.runFrom, for any machine. -/
theorem scan_right {n : Nat} (M : Machine n) (q : Fin n) (bit : Bool)
    (ht : M.transition q bit = { write := bit, move := .right, next := some q })
    (length : Nat) (head : Int) (tape : Tape) (hspan : Span tape head bit length) :
    M.runFrom (atState q head tape) length =
      atState q (head + (length : Int)) tape := by
  revert hspan
  induction length with
  | zero =>
      intro _
      simp only [Machine.runFrom, Int.ofNat_zero, Int.add_zero]
  | succ length ih =>
      intro hspan
      have prev := ih (fun i hi => hspan i (by omega))
      rw [Machine.runFrom_succ, prev]
      have hread := hspan length (by omega)
      have hs := step_preserving M q q (head + (length : Int)) tape bit .right hread ht
      have hp : (head + (length : Int)) + 1 = head + ((length + 1 : Nat) : Int) := by omega
      simpa only [Move.apply, hp] using hs

/- The following are checks of actual frozen table rows, not hypotheses. -/
theorem row_inc_zero :
    Literal.transition inc false = { write := true, move := .right, next := some incGap } := by
  decide

theorem row_gap_zero :
    Literal.transition incGap false = { write := false, move := .right, next := some incGap } := by
  decide

theorem row_gap_one :
    Literal.transition incGap true = { write := true, move := .right, next := some incOnes } := by
  decide

theorem row_ones_one :
    Literal.transition incOnes true = { write := true, move := .right, next := some incOnes } := by
  decide

theorem row_ones_zero :
    Literal.transition incOnes false = { write := false, move := .right, next := some incSeparator } := by
  decide

theorem row_separator_one :
    Literal.transition incSeparator true = { write := true, move := .right, next := some incOnes } := by
  decide

theorem row_separator_zero :
    Literal.transition incSeparator false = { write := true, move := .left, next := some retOne } := by
  decide

theorem row_return_one :
    Literal.transition retOne true = { write := true, move := .left, next := some retOne } := by
  decide

theorem row_return_zero :
    Literal.transition retOne false = { write := false, move := .left, next := some retOneProbe } := by
  decide

theorem row_probe_one :
    Literal.transition retOneProbe true = { write := true, move := .left, next := some retOne } := by
  decide

theorem row_probe_zero :
    Literal.transition retOneProbe false = { write := false, move := .left, next := some retOneMarker } := by
  decide

theorem row_marker_zero :
    Literal.transition retOneMarker false = { write := false, move := .left, next := some retOneMarker } := by
  decide

theorem row_marker_one :
    Literal.transition retOneMarker true = { write := false, move := .left, next := some breakZero } := by
  decide

/-- Width of a sequence of positive unary blocks, including their trailing zeros. -/
def prefixWidth : List Nat → Int
  | [] => 0
  | value :: rest => (value : Int) + 2 + prefixWidth rest

/-- Each preceding register is `1^(value+1) 0`; the prefix starts with a one. -/
def RegisterPrefix (tape : Tape) (head : Int) : List Nat → Prop
  | [] => True
  | value :: rest =>
      Span tape head true (value + 1) ∧
      Tape.read tape (head + (value : Int) + 1) = false ∧
      RegisterPrefix tape (head + (value : Int) + 2) rest

theorem prefixWidth_nonneg (values : List Nat) : 0 ≤ prefixWidth values := by
  induction values with
  | nil => simp only [prefixWidth]; omega
  | cons value rest ih => simp only [prefixWidth]; omega

theorem prefixWidth_pos {values : List Nat} (hne : values ≠ []) : 2 ≤ prefixWidth values := by
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons value rest =>
      have h := prefixWidth_nonneg rest
      simp only [prefixWidth]
      omega

theorem registerPrefix_write_left {tape : Tape} {head pos : Int} {bit : Bool}
    {values : List Nat} (h : RegisterPrefix tape head values) (hp : pos < head) :
    RegisterPrefix (Tape.write tape pos bit) head values := by
  induction values generalizing head with
  | nil => trivial
  | cons value rest ih =>
      rcases h with ⟨hones, hzero, hrest⟩
      refine ⟨span_write_left hones hp, ?_, ih hrest (by omega)⟩
      rw [Tape.read_write_of_ne tape (by omega : head + (value : Int) + 1 ≠ pos) bit]
      exact hzero

/-- Ordinary unary register: a zero boundary, value+1 ones, then a zero. -/
def UnaryRegister (tape : Tape) (first : Int) (value : Nat) : Prop :=
  Tape.read tape (first - 1) = false ∧
  Span tape first true (value + 1) ∧
  Tape.read tape (first + (value : Int) + 1) = false

/-- The movable selector contributes two zeros immediately before a register. -/
def SelectedRegister (tape : Tape) (selector : Int) (value : Nat) : Prop :=
  Tape.read tape selector = false ∧ Tape.read tape (selector + 1) = false ∧
  Span tape (selector + 2) true (value + 1) ∧
  Tape.read tape (selector + (value : Int) + 3) = false

theorem selectedRegister_write_left {tape : Tape} {selector pos : Int}
    {value : Nat} {bit : Bool} (h : SelectedRegister tape selector value)
    (hp : pos < selector) : SelectedRegister (Tape.write tape pos bit) selector value := by
  rcases h with ⟨hzero, hmark, hones, hend⟩
  refine ⟨?_, ?_, span_write_left hones (by omega), ?_⟩
  · rw [Tape.read_write_of_ne tape (by omega : selector ≠ pos) bit]
    exact hzero
  · rw [Tape.read_write_of_ne tape (by omega : selector + 1 ≠ pos) bit]
    exact hmark
  · rw [Tape.read_write_of_ne tape (by omega : selector + (value : Int) + 3 ≠ pos) bit]
    exact hend

/-- Filling the selector's second zero increases the actual unary value by one. -/
theorem selectedRegister_increment {tape : Tape} {selector : Int} {value : Nat}
    (h : SelectedRegister tape selector value) :
    UnaryRegister (Tape.write tape (selector + 1) true) (selector + 1) (value + 1) := by
  rcases h with ⟨hzero, _hmark, hones, hend⟩
  refine ⟨?_, ?_, ?_⟩
  · have hp : selector + 1 - 1 = selector := by omega
    rw [hp, Tape.read_write_of_ne tape (by omega : selector ≠ selector + 1) true]
    exact hzero
  · intro i hi
    by_cases hzero : i = 0
    · subst i
      simp only [Int.ofNat_zero, Int.add_zero, Tape.read_write_same]
    · have hp : selector + 1 + (i : Int) = selector + 2 + ((i - 1 : Nat) : Int) := by omega
      rw [Tape.read_write_of_ne tape (by omega : selector + 1 + (i : Int) ≠ selector + 1) true, hp]
      exact hones (i - 1) (by omega)
  · have hp : selector + 1 + ((value + 1 : Nat) : Int) + 1 =
        selector + (value : Int) + 3 := by omega
    rw [hp, Tape.read_write_of_ne tape (by omega : selector + (value : Int) + 3 ≠ selector + 1) true]
    exact hend

/-- The literal inc.c/inc.d scan crosses arbitrary preceding unary registers.
Its only write is to the second selector zero; the tape elsewhere is untouched. -/
theorem inc_prefix_execution (values : List Nat) (head : Int) (tape : Tape)
    (hprefix : RegisterPrefix tape head values)
    (hfill : Tape.read tape (head + prefixWidth values) = false) :
    Reaches Literal (atState incSeparator head tape)
      (atState retOne (head + prefixWidth values - 1)
        (Tape.write tape (head + prefixWidth values) true)) := by
  induction values generalizing head with
  | nil =>
      have hs := step_writing Literal incSeparator retOne head tape false true .left
        (by simpa only [prefixWidth, Int.add_zero] using hfill) row_separator_zero
      simpa only [prefixWidth, Int.add_zero, Move.apply] using reaches_step hs
  | cons value rest ih =>
      rcases hprefix with ⟨hones, hzero, hrest⟩
      have hfirst : Tape.read tape head = true := by
        simpa only [Int.ofNat_zero, Int.add_zero] using hones 0 (by omega)
      have h1 : Reaches Literal (atState incSeparator head tape)
          (atState incOnes (head + 1) tape) := by
        simpa only [Move.apply] using reaches_step
          (step_preserving Literal incSeparator incOnes head tape true .right hfirst row_separator_one)
      have h2 : Reaches Literal (atState incOnes (head + 1) tape)
          (atState incOnes (head + 1 + (value : Int)) tape) :=
        ⟨value, scan_right Literal incOnes true row_ones_one value (head + 1) tape
          (span_tail hones)⟩
      have hread : Tape.read tape (head + 1 + (value : Int)) = false := by
        have hp : head + 1 + (value : Int) = head + (value : Int) + 1 := by omega
        rw [hp]
        exact hzero
      have h3 : Reaches Literal (atState incOnes (head + 1 + (value : Int)) tape)
          (atState incSeparator (head + (value : Int) + 2) tape) := by
        have hs := step_preserving Literal incOnes incSeparator
          (head + 1 + (value : Int)) tape false .right hread row_ones_zero
        have hp : head + 1 + (value : Int) + 1 = head + (value : Int) + 2 := by omega
        simpa only [Move.apply, hp] using reaches_step hs
      have hp : (head + (value : Int) + 2) + prefixWidth rest =
          head + prefixWidth (value :: rest) := by
        simp only [prefixWidth]
        omega
      have hfill' : Tape.read tape ((head + (value : Int) + 2) + prefixWidth rest) = false := by
        rw [hp]
        exact hfill
      have h4 := ih (head + (value : Int) + 2) hrest hfill'
      have result := reaches_trans h1 (reaches_trans h2 (reaches_trans h3 h4))
      simpa only [hp] using result

/-- The INC scan is an actual unbounded unary-register increment in Table252. -/
theorem inc_prefix_register_effect (values : List Nat) (head : Int) (tape : Tape)
    (value : Nat) (hprefix : RegisterPrefix tape head values)
    (hselected : SelectedRegister tape (head + prefixWidth values - 1) value) :
    ∃ finalTape,
      Reaches Literal (atState incSeparator head tape)
        (atState retOne (head + prefixWidth values - 1) finalTape) ∧
      UnaryRegister finalTape (head + prefixWidth values) (value + 1) ∧
      (∀ pos, pos ≠ head + prefixWidth values →
        Tape.read finalTape pos = Tape.read tape pos) := by
  have hp : (head + prefixWidth values - 1) + 1 = head + prefixWidth values := by omega
  have hfill : Tape.read tape (head + prefixWidth values) = false := by
    simpa only [hp] using hselected.2.1
  refine ⟨Tape.write tape (head + prefixWidth values) true,
    inc_prefix_execution values head tape hprefix hfill, ?_, ?_⟩
  · simpa only [hp] using selectedRegister_increment hselected
  · intro pos hpos
    exact Tape.read_write_of_ne tape hpos true

/-- The first prefix one is consumed by inc.b before the register scan begins. -/
theorem inc_after_first_one_execution (first : Nat) (rest : List Nat)
    (head : Int) (tape : Tape)
    (hprefix : RegisterPrefix tape head (first :: rest))
    (hfill : Tape.read tape (head + prefixWidth (first :: rest)) = false) :
    Reaches Literal (atState incOnes (head + 1) tape)
      (atState retOne (head + prefixWidth (first :: rest) - 1)
        (Tape.write tape (head + prefixWidth (first :: rest)) true)) := by
  rcases hprefix with ⟨hones, hzero, hrest⟩
  have hscan : Reaches Literal (atState incOnes (head + 1) tape)
      (atState incOnes (head + 1 + (first : Int)) tape) :=
    ⟨first, scan_right Literal incOnes true row_ones_one first (head + 1) tape
      (span_tail hones)⟩
  have hread : Tape.read tape (head + 1 + (first : Int)) = false := by
    have hp : head + 1 + (first : Int) = head + (first : Int) + 1 := by omega
    rw [hp]
    exact hzero
  have hsep : Reaches Literal (atState incOnes (head + 1 + (first : Int)) tape)
      (atState incSeparator (head + (first : Int) + 2) tape) := by
    have hs := step_preserving Literal incOnes incSeparator
      (head + 1 + (first : Int)) tape false .right hread row_ones_zero
    have hp : head + 1 + (first : Int) + 1 = head + (first : Int) + 2 := by omega
    simpa only [Move.apply, hp] using reaches_step hs
  have hp : (head + (first : Int) + 2) + prefixWidth rest =
      head + prefixWidth (first :: rest) := by
    simp only [prefixWidth]
    omega
  have hfill' : Tape.read tape ((head + (first : Int) + 2) + prefixWidth rest) = false := by
    rw [hp]
    exact hfill
  have htail := inc_prefix_execution rest (head + (first : Int) + 2) tape hrest hfill'
  simpa only [hp] using reaches_trans hscan (reaches_trans hsep htail)

def prefixBase (marker : Int) (gap : Nat) : Int := marker + 1 + (gap : Int)

/-- INC entry: the temporary marker is still zero, followed by a zero gap,
nonempty preceding unary blocks, and a selected register. -/
structure IncrementInput (tape : Tape) (marker : Int) (gap : Nat)
    (preceding : List Nat) (value : Nat) : Prop where
  entryZero : Tape.read tape marker = false
  gapZero : Span tape (marker + 1) false gap
  prefixNonempty : preceding ≠ []
  prefixBlocks : RegisterPrefix tape (prefixBase marker gap) preceding
  selectedBlock : SelectedRegister tape
    (prefixBase marker gap + prefixWidth preceding - 1) value

/-- Actual states 13 and 14 write the temporary marker and cross any zero gap. -/
theorem inc_gap_execution (gap : Nat) (marker : Int) (tape : Tape)
    (hzero : Tape.read tape marker = false)
    (hgap : Span tape (marker + 1) false gap)
    (hfirst : Tape.read tape (prefixBase marker gap) = true) :
    Reaches Literal (atState inc marker tape)
      (atState incOnes (prefixBase marker gap + 1) (Tape.write tape marker true)) := by
  let marked := Tape.write tape marker true
  have h1 : Reaches Literal (atState inc marker tape)
      (atState incGap (marker + 1) marked) := by
    simpa only [Move.apply] using reaches_step
      (step_writing Literal inc incGap marker tape false true .right hzero row_inc_zero)
  have hgap' : Span marked (marker + 1) false gap :=
    span_write_left hgap (by omega)
  have h2 : Reaches Literal (atState incGap (marker + 1) marked)
      (atState incGap (prefixBase marker gap) marked) :=
    ⟨gap, scan_right Literal incGap false row_gap_zero gap (marker + 1) marked hgap'⟩
  have hpos : prefixBase marker gap ≠ marker := by simp only [prefixBase]; omega
  have hread : Tape.read marked (prefixBase marker gap) = true := by
    rw [Tape.read_write_of_ne tape hpos true]
    exact hfirst
  have h3 : Reaches Literal (atState incGap (prefixBase marker gap) marked)
      (atState incOnes (prefixBase marker gap + 1) marked) := by
    simpa only [Move.apply] using reaches_step
      (step_preserving Literal incGap incOnes (prefixBase marker gap) marked true .right hread row_gap_one)
  exact reaches_trans h1 (reaches_trans h2 h3)

/-- Full outward INC excursion of the literal 252-state engine. It starts at
1.inc, reaches 2.ret1, increments the selected unary value, and changes only
the temporary marker and the filled selector zero. PC return is separate. -/
theorem increment_execution (tape : Tape) (marker : Int) (gap : Nat)
    (preceding : List Nat) (value : Nat) (h : IncrementInput tape marker gap preceding value) :
    ∃ finalTape,
      Reaches Literal (atState inc marker tape)
        (atState retOne (prefixBase marker gap + prefixWidth preceding - 1) finalTape) ∧
      UnaryRegister finalTape (prefixBase marker gap + prefixWidth preceding) (value + 1) ∧
      Tape.read finalTape marker = true ∧
      (∀ pos, pos ≠ marker → pos ≠ prefixBase marker gap + prefixWidth preceding →
        Tape.read finalTape pos = Tape.read tape pos) := by
  let marked := Tape.write tape marker true
  have hbase : marker < prefixBase marker gap := by simp only [prefixBase]; omega
  have hwidth := prefixWidth_pos h.prefixNonempty
  have hmarker : marker < prefixBase marker gap + prefixWidth preceding - 1 := by omega
  have hblocks : RegisterPrefix marked (prefixBase marker gap) preceding :=
    registerPrefix_write_left h.prefixBlocks hbase
  have hselected : SelectedRegister marked
      (prefixBase marker gap + prefixWidth preceding - 1) value :=
    selectedRegister_write_left h.selectedBlock hmarker
  have hfillpos : (prefixBase marker gap + prefixWidth preceding - 1) + 1 =
      prefixBase marker gap + prefixWidth preceding := by omega
  have hfill : Tape.read marked (prefixBase marker gap + prefixWidth preceding) = false := by
    simpa only [hfillpos] using hselected.2.1
  have hfirst : Tape.read tape (prefixBase marker gap) = true := by
    cases preceding with
    | nil => exact False.elim (h.prefixNonempty rfl)
    | cons first rest =>
        simpa only [Int.ofNat_zero, Int.add_zero] using h.prefixBlocks.1 0 (by omega)
  have hgapRun := inc_gap_execution gap marker tape h.entryZero h.gapZero hfirst
  have hscanRun : Reaches Literal
      (atState incOnes (prefixBase marker gap + 1) marked)
      (atState retOne (prefixBase marker gap + prefixWidth preceding - 1)
        (Tape.write marked (prefixBase marker gap + prefixWidth preceding) true)) := by
    cases preceding with
    | nil => exact False.elim (h.prefixNonempty rfl)
    | cons first rest =>
        exact inc_after_first_one_execution first rest (prefixBase marker gap) marked hblocks hfill
  refine ⟨Tape.write marked (prefixBase marker gap + prefixWidth preceding) true,
    reaches_trans hgapRun hscanRun, ?_, ?_, ?_⟩
  · simpa only [hfillpos] using selectedRegister_increment hselected
  · rw [Tape.read_write_of_ne marked (by omega : marker ≠ prefixBase marker gap + prefixWidth preceding) true]
    exact Tape.read_write_same tape marker true
  · intro pos hmarker' hfill'
    rw [Tape.read_write_of_ne marked hfill' true,
      Tape.read_write_of_ne tape hmarker' true]

/-- A finite interval read from right to left. -/
def BackSpan (tape : Tape) (head : Int) (bit : Bool) (length : Nat) : Prop :=
  ∀ i : Nat, i < length → Tape.read tape (head - (i : Int)) = bit

theorem span_reverse {tape : Tape} {head : Int} {bit : Bool} {length : Nat}
    (h : Span tape head bit (length + 1)) :
    BackSpan tape (head + (length : Int) - 1) bit length := by
  intro i hi
  have hp : head + (length : Int) - 1 - (i : Int) =
      head + ((length - 1 - i : Nat) : Int) := by omega
  rw [hp]
  exact h (length - 1 - i) (by omega)

theorem scan_left {n : Nat} (M : Machine n) (q : Fin n) (bit : Bool)
    (ht : M.transition q bit = { write := bit, move := .left, next := some q })
    (length : Nat) (head : Int) (tape : Tape) (hspan : BackSpan tape head bit length) :
    M.runFrom (atState q head tape) length =
      atState q (head - (length : Int)) tape := by
  revert hspan
  induction length with
  | zero =>
      intro _
      simp only [Machine.runFrom, Int.ofNat_zero, Int.sub_zero]
  | succ length ih =>
      intro hspan
      have prev := ih (fun i hi => hspan i (by omega))
      rw [Machine.runFrom_succ, prev]
      have hread := hspan length (by omega)
      have hs := step_preserving M q q (head - (length : Int)) tape bit .left hread ht
      have hp : (head - (length : Int)) - 1 = head - ((length + 1 : Nat) : Int) := by omega
      simpa only [Move.apply, hp] using hs

/-- Return across all preceding unary blocks preserves the entire tape. -/
theorem return_prefix_execution (values : List Nat) (head : Int) (tape : Tape)
    (hprefix : RegisterPrefix tape head values) :
    Reaches Literal (atState retOne (head + prefixWidth values - 1) tape)
      (atState retOne (head - 1) tape) := by
  induction values generalizing head with
  | nil =>
      simpa only [prefixWidth, Int.add_zero] using
        reaches_refl Literal (atState retOne (head - 1) tape)
  | cons value rest ih =>
      rcases hprefix with ⟨hones, hzero, hrest⟩
      have hp : (head + (value : Int) + 2) + prefixWidth rest - 1 =
          head + prefixWidth (value :: rest) - 1 := by
        simp only [prefixWidth]
        omega
      have hp' : head + (value : Int) + 2 - 1 = head + (value : Int) + 1 := by omega
      have htail : Reaches Literal
          (atState retOne (head + prefixWidth (value :: rest) - 1) tape)
          (atState retOne (head + (value : Int) + 1) tape) := by
        simpa only [hp, hp'] using ih (head + (value : Int) + 2) hrest
      have h1 : Reaches Literal (atState retOne (head + (value : Int) + 1) tape)
          (atState retOneProbe (head + (value : Int)) tape) := by
        have hs := step_preserving Literal retOne retOneProbe
          (head + (value : Int) + 1) tape false .left hzero row_return_zero
        have hpos : head + (value : Int) + 1 - 1 = head + (value : Int) := by omega
        simpa only [Move.apply, hpos] using reaches_step hs
      have hlast : Tape.read tape (head + (value : Int)) = true := hones value (by omega)
      have h2 : Reaches Literal (atState retOneProbe (head + (value : Int)) tape)
          (atState retOne (head + (value : Int) - 1) tape) := by
        simpa only [Move.apply] using reaches_step
          (step_preserving Literal retOneProbe retOne (head + (value : Int)) tape true .left hlast row_probe_one)
      have h3 : Reaches Literal (atState retOne (head + (value : Int) - 1) tape)
          (atState retOne (head - 1) tape) := by
        have hs := scan_left Literal retOne true row_return_one value
          (head + (value : Int) - 1) tape (span_reverse hones)
        have hpos : head + (value : Int) - 1 - (value : Int) = head - 1 := by omega
        exact ⟨value, by simpa only [hpos] using hs⟩
      exact reaches_trans htail (reaches_trans h1 (reaches_trans h2 h3))

/-- Literal return states find and erase the temporary marker, then hand
control to the existing PC increment state. At least two gap zeros remain. -/
theorem return_one_execution (values : List Nat) (marker : Int) (gap : Nat)
    (tape : Tape) (hgapLength : 2 ≤ gap)
    (hmarker : Tape.read tape marker = true)
    (hgap : Span tape (marker + 1) false gap)
    (hprefix : RegisterPrefix tape (prefixBase marker gap) values) :
    Reaches Literal
      (atState retOne (prefixBase marker gap + prefixWidth values - 1) tape)
      (atState breakZero (marker - 1) (Tape.write tape marker false)) := by
  obtain ⟨extra, rfl⟩ : ∃ extra : Nat, gap = extra + 2 := ⟨gap - 2, by omega⟩
  have hp : prefixBase marker (extra + 2) - 1 = marker + (extra : Int) + 2 := by
    simp only [prefixBase]
    omega
  have h0 : Reaches Literal
      (atState retOne (prefixBase marker (extra + 2) + prefixWidth values - 1) tape)
      (atState retOne (marker + (extra : Int) + 2) tape) := by
    simpa only [hp] using return_prefix_execution values (prefixBase marker (extra + 2)) tape hprefix
  have hz1 : Tape.read tape (marker + (extra : Int) + 2) = false := by
    have hpos : marker + 1 + ((extra + 1 : Nat) : Int) = marker + (extra : Int) + 2 := by omega
    simpa only [hpos] using hgap (extra + 1) (by omega)
  have h1 : Reaches Literal (atState retOne (marker + (extra : Int) + 2) tape)
      (atState retOneProbe (marker + (extra : Int) + 1) tape) := by
    have hs := step_preserving Literal retOne retOneProbe (marker + (extra : Int) + 2)
      tape false .left hz1 row_return_zero
    have hpos : marker + (extra : Int) + 2 - 1 = marker + (extra : Int) + 1 := by omega
    simpa only [Move.apply, hpos] using reaches_step hs
  have hz2 : Tape.read tape (marker + (extra : Int) + 1) = false := by
    have hpos : marker + 1 + (extra : Int) = marker + (extra : Int) + 1 := by omega
    simpa only [hpos] using hgap extra (by omega)
  have h2 : Reaches Literal (atState retOneProbe (marker + (extra : Int) + 1) tape)
      (atState retOneMarker (marker + (extra : Int)) tape) := by
    have hs := step_preserving Literal retOneProbe retOneMarker
      (marker + (extra : Int) + 1) tape false .left hz2 row_probe_zero
    have hpos : marker + (extra : Int) + 1 - 1 = marker + (extra : Int) := by omega
    simpa only [Move.apply, hpos] using reaches_step hs
  have hsmall : Span tape (marker + 1) false (extra + 1) :=
    fun i hi => hgap i (by omega)
  have hback : BackSpan tape (marker + (extra : Int)) false extra := by
    have hpos : marker + 1 + (extra : Int) - 1 = marker + (extra : Int) := by omega
    simpa only [hpos] using span_reverse hsmall
  have h3 : Reaches Literal (atState retOneMarker (marker + (extra : Int)) tape)
      (atState retOneMarker marker tape) := by
    have hs := scan_left Literal retOneMarker false row_marker_zero extra
      (marker + (extra : Int)) tape hback
    have hpos : marker + (extra : Int) - (extra : Int) = marker := by omega
    exact ⟨extra, by simpa only [hpos] using hs⟩
  have h4 : Reaches Literal (atState retOneMarker marker tape)
      (atState breakZero (marker - 1) (Tape.write tape marker false)) := by
    simpa only [Move.apply] using reaches_step
      (step_writing Literal retOneMarker breakZero marker tape true false .left hmarker row_marker_one)
  exact reaches_trans h0 (reaches_trans h1 (reaches_trans h2 (reaches_trans h3 h4)))

theorem registerPrefix_congr {tape tape' : Tape} {head : Int} {values : List Nat}
    (hprefix : RegisterPrefix tape head values)
    (hagree : ∀ pos, head ≤ pos → pos < head + prefixWidth values →
      Tape.read tape' pos = Tape.read tape pos) : RegisterPrefix tape' head values := by
  induction values generalizing head with
  | nil => trivial
  | cons value rest ih =>
      rcases hprefix with ⟨hones, hzero, hrest⟩
      have hwidth := prefixWidth_nonneg rest
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [hagree (head + (i : Int)) (by omega) (by simp only [prefixWidth]; omega)]
        exact hones i hi
      · rw [hagree (head + (value : Int) + 1) (by omega) (by simp only [prefixWidth]; omega)]
        exact hzero
      · apply ih hrest
        intro pos hlo hhi
        exact hagree pos (by omega) (by simp only [prefixWidth]; omega)

theorem unaryRegister_write_left {tape : Tape} {first pos : Int} {value : Nat}
    {bit : Bool} (h : UnaryRegister tape first value) (hp : pos < first - 1) :
    UnaryRegister (Tape.write tape pos bit) first value := by
  rcases h with ⟨hzero, hones, hend⟩
  refine ⟨?_, span_write_left hones (by omega), ?_⟩
  · rw [Tape.read_write_of_ne tape (by omega : first - 1 ≠ pos) bit]
    exact hzero
  · rw [Tape.read_write_of_ne tape (by omega : first + (value : Int) + 1 ≠ pos) bit]
    exact hend

/-- INC plus its entire RF/gap return reaches the PC carry state. The selected
register increases by one and every other tape cell has its original value. -/
theorem increment_return_execution (tape : Tape) (marker : Int) (gap : Nat)
    (preceding : List Nat) (value : Nat)
    (h : IncrementInput tape marker gap preceding value) (hgapLength : 2 ≤ gap) :
    ∃ finalTape,
      Reaches Literal (atState inc marker tape) (atState breakZero (marker - 1) finalTape) ∧
      UnaryRegister finalTape (prefixBase marker gap + prefixWidth preceding) (value + 1) ∧
      (∀ pos, pos ≠ prefixBase marker gap + prefixWidth preceding →
        Tape.read finalTape pos = Tape.read tape pos) := by
  obtain ⟨middle, hrun, hvalue, hmarker, hframe⟩ := increment_execution tape marker gap preceding value h
  have hbase : marker < prefixBase marker gap := by simp only [prefixBase]; omega
  have hwidth := prefixWidth_pos h.prefixNonempty
  have hprefix : RegisterPrefix middle (prefixBase marker gap) preceding := by
    apply registerPrefix_congr h.prefixBlocks
    intro pos hlo hhi
    exact hframe pos (by omega) (by omega)
  have hgap : Span middle (marker + 1) false gap := by
    intro i hi
    have hpos : marker + 1 + (i : Int) < prefixBase marker gap := by
      simp only [prefixBase]
      omega
    rw [hframe (marker + 1 + (i : Int)) (by omega) (by omega)]
    exact h.gapZero i hi
  have hreturn := return_one_execution preceding marker gap middle hgapLength hmarker hgap hprefix
  refine ⟨Tape.write middle marker false, reaches_trans hrun hreturn,
    unaryRegister_write_left hvalue (by omega), ?_⟩
  intro pos hfill
  by_cases hpos : pos = marker
  · subst pos
    rw [Tape.read_write_same, h.entryZero]
  · rw [Tape.read_write_of_ne middle hpos false]
    exact hframe pos hpos hfill

#print axioms scan_right
#print axioms inc_prefix_execution
#print axioms inc_prefix_register_effect
#print axioms increment_execution
#print axioms return_one_execution
#print axioms increment_return_execution

end SetTheory.BusyBeaver.ZFC.WadeMachine
