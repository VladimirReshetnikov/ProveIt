import BusyBeaver.ZFC.ArithmeticCommandRun254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254
open ArithmeticCommandTick254 ArithmeticCommandRun254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.live_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.remaining_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.working_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.live_decode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.next_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.tick_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.tick_live_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.tick_stopped
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandTick254.tick_decreases
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.run_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.run_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.run_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.run_stopped
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.run_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.drain_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.drained
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.terminal_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.eval_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.eval_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.eval_zero_word
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.terminal_stopped
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.eval_eq_zero_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.totalitySentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.isigma1_proves_totality
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRun254.peano_proves_totality
section IOpen
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (out word w : V) : liveDef.val.Evalb ![out,word,w] ↔ out = liveValue word w := by simp
example (out config : V) : remainingDef.val.Evalb ![out,config] ↔ out = remaining config := by simp
example (out config : V) : workingDef.val.Evalb ![out,config] ↔ out = working config := by simp
example (config : V) (hc : config ≠ 0) :
    liveValue (remaining config) (working config) = config := live_decode config hc
example (out raw w : V) : nextDef.val.Evalb ![out,raw,w] ↔ out = nextValue raw w := by simp
example (out config : V) : tickDef.val.Evalb ![out,config] ↔ out = tickValue config := by simp
example (config : V) : ∃! out, tickDef.val.Evalb ![out,config] := by simp
example (w : V) : tickValue (liveValue 0 w) = liveValue 0 w := tick_done w
example (w : V) : tickValue (liveValue 1 w) = nextValue 0 w := by
  simpa only [zero_add] using tick_live_succ (0 : V) w
example (raw w : V) : tickValue (liveValue (raw+1) w) = nextValue raw w := tick_live_succ raw w
example (config : V) (hc : Stopped config) : tickValue config = config := tick_stopped hc
example (config : V) (hc : ¬ Stopped config) :
    tickValue config = 0 ∨ remaining (tickValue config)+1 ≤ remaining config := tick_decreases hc
end IOpen
section ISigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out time initial : V) : runDef.val.Evalb ![out,time,initial] ↔ out = run time initial := by simp
example (time initial : V) : ∃! out, runDef.val.Evalb ![out,time,initial] := run_total time initial
example (time initial : V) (hi : Stopped initial) : run time initial = initial := run_stopped time initial hi
example (time : V) : run time 0 = 0 := run_halted time
example (time w : V) : run time (liveValue 0 w) = liveValue 0 w := run_done time w
example (first second initial : V) :
    run (first+second) initial = run second (run first initial) := run_add first second initial
example (time word w : V) : Stopped (run time (liveValue word w)) ∨
    remaining (run time (liveValue word w))+time ≤ word := drain_bound time word w
example (word w : V) : Stopped (run word (liveValue word w)) := drained word w
example (word w : V) : Stopped (terminal word w) := terminal_stopped word w
example (out word w : V) : terminalDef.val.Evalb ![out,word,w] ↔ out = terminal word w := by simp
example (out word w : V) : evalDef.val.Evalb ![out,word,w] ↔ out = evalValue word w := by simp
example (word w : V) : ∃! out, evalDef.val.Evalb ![out,word,w] := eval_total word w
example (w : V) : evalValue 0 w = w+1 := eval_zero_word w
example (word w : V) : evalValue word w = 0 ↔ terminal word w = 0 := eval_eq_zero_iff word w
example : totalitySentence.Evalb (M := V) ![] := totalitySentence_true
end ISigma1
example : 𝗜𝚺₁ ⊢ totalitySentence := isigma1_proves_totality
example : Peano ⊢ totalitySentence := peano_proves_totality

/-- Explicit native dictionary binding: shifted word1's raw head0 is MP0,
whereas shifted word0 has the successful identity evaluator above. -/
example (w : Enum254.W) :
    stepValue 0 (encodeW w) = encodeResult (Enum254.cstep (.mp 0) w) := by
  have hp : Enum254.pack (.mp 0) 0 = 0 := by decide
  simpa only [hp] using stepValue_pack_nat (.mp 0) 0 w
