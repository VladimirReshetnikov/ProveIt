import BusyBeaver.ZFC.ArithmeticCommandRun254

/-!
All-Nat comparison with the actual Enum254.cexec function.
The list-length run ends at the exact encoded native result, and the checked
absorbing semantics retain that result until the evaluator's numerical word
bound. Total decoding then covers every shifted word code and working-state
code. No list execution is assumed inside a nonstandard arithmetic model.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254
open ArithmeticCommandTick254 ArithmeticCommandRun254
attribute [local irreducible] Code254.P Enum254.pack
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Halt0 or a positive completed evaluator, retaining the exact final W. -/
noncomputable def encodeTerminalResult : Option Enum254.W → Nat
  | none => 0
  | some w => liveValue 0 (encodeW w)

/-- The active shifted word is unshifted exactly once. This is the actual
native cstep on its head, and the actual word tail on its successful branch. -/
theorem tick_encode_cons (c : Enum254.Cmd) (cs : List Enum254.Cmd) (w : Enum254.W) :
    tickValue (liveValue (CommandWord254.encode (c :: cs)) (encodeW w)) =
      match Enum254.cstep c w with
      | none => 0
      | some w' => liveValue (CommandWord254.encode cs) (encodeW w') := by
  rw [show CommandWord254.encode (c :: cs) =
    Enum254.pack c (CommandWord254.encode cs) + 1 from rfl, tick_live_succ]
  unfold nextValue
  rw [stepValue_pack_nat, tailValue_nat, CommandWord254.tail_pack]
  cases hc : Enum254.cstep c w with
  | none => simp [encodeResult]
  | some w' => simp [encodeResult]

/-- Same internal semigroup theorem, specialized to the ordinary Nat time
whose first tick executes the actual head command above. -/
lemma run_succ_first (time initial : Nat) :
    run (time + 1) initial = run time (tickValue initial) := by
  rw [show time + 1 = 1 + time by omega, run_add]
  have hone : run 1 initial = tickValue initial := by
    simpa only [zero_add, run_zero] using run_succ (0 : Nat) initial
  rw [hone]

/-- Exactly the actual native cexec result, at every finite list's own length.
Early halting remains0 through the unused suffix; no list is silently resumed. -/
theorem run_length (cs : List Enum254.Cmd) (w : Enum254.W) :
    run cs.length (liveValue (CommandWord254.encode cs) (encodeW w)) =
      encodeTerminalResult (Enum254.cexec cs w) := by
  induction cs generalizing w with
  | nil => simp only [List.length_nil, run_zero, Enum254.cexec, encodeTerminalResult]; rfl
  | cons c cs ih =>
    rw [List.length_cons, run_succ_first, tick_encode_cons]
    cases hc : Enum254.cstep c w with
    | none => simp [hc, Enum254.cexec, encodeTerminalResult]
    | some w' => simpa only [Enum254.cexec, hc] using ih w'

/-- Ordinary list length never exceeds its shifted word code. This uses the
actual unpack-rest bound, not a bound on the gigantic formula payloads. -/
theorem length_le_encode (cs : List Enum254.Cmd) :
    @LE.le Nat instLENat cs.length (CommandWord254.encode cs) := by
  induction cs with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    have ht : @LE.le Nat instLENat (CommandWord254.encode cs) (Enum254.pack c (CommandWord254.encode cs)) := by
      simpa only [CommandWord254.tail_pack] using
        CommandWord254.tail_le (Enum254.pack c (CommandWord254.encode cs))
    exact Nat.succ_le_succ (Nat.le_trans ih ht)

/-- The numeric terminal time may exceed list length; both actual outcomes
are absorbing, so the result agrees without a termination cutoff assumption. -/
theorem terminal_encode (cs : List Enum254.Cmd) (w : Enum254.W) :
    terminal (CommandWord254.encode cs) (encodeW w) =
      encodeTerminalResult (Enum254.cexec cs w) := by
  obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (length_le_encode cs)
  unfold terminal
  calc
    run (CommandWord254.encode cs) (liveValue (CommandWord254.encode cs) (encodeW w)) =
        run (cs.length + extra) (liveValue (CommandWord254.encode cs) (encodeW w)) :=
      congrArg (fun time : Nat => run time (liveValue (CommandWord254.encode cs) (encodeW w))) he
    _ = run extra (run cs.length (liveValue (CommandWord254.encode cs) (encodeW w))) :=
      run_add cs.length extra _
    _ = encodeTerminalResult (Enum254.cexec cs w) := by
      rw [run_length]
      cases hc : Enum254.cexec cs w with
      | none => simp [encodeTerminalResult]
      | some w' => simp [encodeTerminalResult]

/-- Complete all-list comparison, not merely compiler-generated words. -/
theorem eval_encode (cs : List Enum254.Cmd) (w : Enum254.W) :
    evalValue (CommandWord254.encode cs) (encodeW w) =
      encodeResult (Enum254.cexec cs w) := by
  unfold evalValue
  rw [terminal_encode]
  cases hc : Enum254.cexec cs w with
  | none => simp [encodeTerminalResult, encodeResult]
  | some w' => simp [encodeTerminalResult, encodeResult]

/-- Every Nat is a shifted finite word; candidate0 and empty word0 remain
separate because the checked total decode/encode bijection is used here. -/
theorem terminal_word (word : Nat) (w : Enum254.W) :
    terminal word (encodeW w) =
      encodeTerminalResult (Enum254.cexec (CommandWord254.decode word) w) := by
  simpa only [CommandWord254.encode_decode] using terminal_encode (CommandWord254.decode word) w

theorem eval_word (word : Nat) (w : Enum254.W) :
    evalValue word (encodeW w) = encodeResult (Enum254.cexec (CommandWord254.decode word) w) := by
  simpa only [CommandWord254.encode_decode] using eval_encode (CommandWord254.decode word) w

/-- The four actual W fields decoded from an arbitrary unshifted Nat code. -/
noncomputable def decodeW (code : Nat) : Enum254.W :=
  ⟨first code, first (second code), first (second (second code)),
    second (second (second code))⟩

@[simp] theorem encodeW_decodeW (code : Nat) : encodeW (decodeW code) = code := by
  simp only [decodeW, encodeW, ← cantor_nat, cantor_projections]

/-- Every pair of word/working-state codes, with no validity or fuel premise. -/
theorem terminal_all_nat (word workingCode : Nat) :
    terminal word workingCode = encodeTerminalResult
      (Enum254.cexec (CommandWord254.decode word) (decodeW workingCode)) := by
  simpa only [encodeW_decodeW] using terminal_word word (decodeW workingCode)

theorem eval_all_nat (word workingCode : Nat) :
    evalValue word workingCode = encodeResult
      (Enum254.cexec (CommandWord254.decode word) (decodeW workingCode)) := by
  simpa only [encodeW_decodeW] using eval_word word (decodeW workingCode)

theorem evalDef_all_nat (out word workingCode : Nat) :
    evalDef.val.Evalb ![out,word,workingCode] ↔ out = encodeResult
      (Enum254.cexec (CommandWord254.decode word) (decodeW workingCode)) := by
  simp [eval_all_nat]

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254
