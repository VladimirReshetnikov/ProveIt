import BusyBeaver.ZFC.ArithmeticCommandRunNat254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCommandStep254 ArithmeticCommandTick254 ArithmeticCommandRun254
open ArithmeticCommandRunNat254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.tick_encode_cons
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.run_succ_first
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.run_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.length_le_encode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.terminal_encode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.eval_encode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.terminal_word
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.eval_word
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.encodeW_decodeW
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.terminal_all_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.eval_all_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRunNat254.evalDef_all_nat
example (c : Enum254.Cmd) (cs : List Enum254.Cmd) (w : Enum254.W) :
    tickValue (liveValue (CommandWord254.encode (c::cs)) (encodeW w)) =
      match Enum254.cstep c w with
      | none => 0
      | some w' => liveValue (CommandWord254.encode cs) (encodeW w') := tick_encode_cons c cs w
example (cs : List Enum254.Cmd) (w : Enum254.W) :
    run cs.length (liveValue (CommandWord254.encode cs) (encodeW w)) =
      encodeTerminalResult (Enum254.cexec cs w) := run_length cs w
example (cs : List Enum254.Cmd) : @LE.le Nat instLENat cs.length (CommandWord254.encode cs) := length_le_encode cs
example (cs : List Enum254.Cmd) (w : Enum254.W) :
    terminal (CommandWord254.encode cs) (encodeW w) =
      encodeTerminalResult (Enum254.cexec cs w) := terminal_encode cs w
example (cs : List Enum254.Cmd) (w : Enum254.W) :
    evalValue (CommandWord254.encode cs) (encodeW w) = encodeResult (Enum254.cexec cs w) := eval_encode cs w
example (word : Nat) (w : Enum254.W) :
    terminal word (encodeW w) = encodeTerminalResult (Enum254.cexec (CommandWord254.decode word) w) := terminal_word word w
example (word : Nat) (w : Enum254.W) :
    evalValue word (encodeW w) = encodeResult (Enum254.cexec (CommandWord254.decode word) w) := eval_word word w
example (code : Nat) : encodeW (decodeW code) = code := encodeW_decodeW code
example (word workingCode : Nat) :
    terminal word workingCode = encodeTerminalResult (Enum254.cexec (CommandWord254.decode word) (decodeW workingCode)) := terminal_all_nat word workingCode
example (word workingCode : Nat) :
    evalValue word workingCode = encodeResult (Enum254.cexec (CommandWord254.decode word) (decodeW workingCode)) := eval_all_nat word workingCode
example (out word workingCode : Nat) :
    evalDef.val.Evalb ![out,word,workingCode] ↔ out = encodeResult
      (Enum254.cexec (CommandWord254.decode word) (decodeW workingCode)) := evalDef_all_nat out word workingCode
example (x : Nat) (cs : List Enum254.Cmd) (w : Enum254.W) :
    evalValue (CommandWord254.encode (.mp x::cs)) (encodeW w) = encodeResult (Enum254.cexec (.mp x::cs) w) := eval_encode _ w
example (x : Nat) (cs : List Enum254.Cmd) (w : Enum254.W) :
    evalValue (CommandWord254.encode (.drop x::cs)) (encodeW w) = encodeResult (Enum254.cexec (.drop x::cs) w) := eval_encode _ w
example (x : Nat) (cs : List Enum254.Cmd) (w : Enum254.W) :
    evalValue (CommandWord254.encode (.nip x::cs)) (encodeW w) = encodeResult (Enum254.cexec (.nip x::cs) w) := eval_encode _ w
example (c x y u : Nat) (cs : List Enum254.Cmd) (w : Enum254.W) :
    evalValue (CommandWord254.encode (.ax c x y u::cs)) (encodeW w) = encodeResult (Enum254.cexec (.ax c x y u::cs) w) := eval_encode _ w
