import BusyBeaver.ZFC.ArithmeticEnumeratorRun254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.embed_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.step_embed_active
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.run_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.run_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.run_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.run_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.run_halted
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.run_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.run_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.paired_or_stopped
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.drain_terminal
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.embed_terminal_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.drain
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.drain_boundary
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.reach
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254.halts_of_word
example (initial : V) : run 0 initial = initial := run_zero initial
example (time : V) : run time 0 = 0 := run_halted time
example (first second initial : V) :
    run (first+second) initial = run second (run first initial) := run_add first second initial
example (time initial : V) : ∃! out, runDef.val.Evalb ![out,time,initial] := run_total time initial
example (np word w : V) :
    embedValue np (ArithmeticCommandTick254.liveValue word w) = liveValue word np w :=
  embed_live np word w
example (np config : V) (h : ¬ ArithmeticCommandTick254.Stopped config) :
    step (embedValue np config) = embedValue np (ArithmeticCommandTick254.tickValue config) :=
  step_embed_active np config h
example (word np w : V) : ∃ t ≤ word,
    run t (liveValue word np w) = embedValue np (ArithmeticCommandRun254.terminal word w) :=
  drain_terminal word np w
example (word np w : V) : ∃ t ≤ word,
    run t (liveValue word np w) = if ArithmeticCommandRun254.evalValue word w = 0 then 0
      else liveValue 0 np (ArithmeticCommandRun254.evalValue word w-1) := drain word np w
example (c w : V) : ∃ t ≤ c+1,
    run t (liveValue 0 c w) = if ArithmeticCommandRun254.evalValue (c+1) w = 0 then 0
      else liveValue 0 (c+1) (ArithmeticCommandRun254.evalValue (c+1) w-1) := drain_boundary c w
example (c w : V) : ∃ time,
    run time (liveValue 0 0 w) = 0 ∨ ∃ w', run time (liveValue 0 0 w) = liveValue 0 c w' :=
  reach c w
example (word w : V) (hp : word ≠ 0) (h : ∀ v, ArithmeticCommandRun254.evalValue word v = 0) :
    ∃ time, run time (liveValue 0 0 w) = 0 := halts_of_word word w hp h
example (c w : V) : run 1 (liveValue 0 c w) = advanceValue c (c+1) w := by
  rw [run_one, step_boundary]
example (w : V) : ArithmeticCommandRun254.evalValue 0 w ≠ 0 := by simp
