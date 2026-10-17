import BusyBeaver.ZFC.ArithmeticCommandExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCommandTick254 ArithmeticCommandRun254 ArithmeticCommandAppend254
open ArithmeticCommandExecution254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.extend_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.extend_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.tick_extend_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.tick_extend_active
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.run_eq_of_stopped_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.stopped_runs_eq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.terminal_eq_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.run_one_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.terminal_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.eval_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.paired_or_stopped
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.stopped_pair
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.terminal_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.eval_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.eval_append_eq_zero
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out right config : V) : extendDef.val.Evalb ![out,right,config] ↔ out=extendValue right config := by simp
example (right config : V) : ∃! out, extendDef.val.Evalb ![out,right,config] := by simp
example (right : V) : extendValue right 0=0 := extend_zero right
example (right w : V) : extendValue right (liveValue 0 w)=liveValue right w := extend_done right w
example (right config : V) (hc : ¬Stopped config) :
    tickValue (extendValue right config)=extendValue right (tickValue config) := tick_extend_active right config hc
example (t u initial : V) (ht : Stopped (run t initial)) (hu : Stopped (run u initial)) :
    run t initial=run u initial := stopped_runs_eq t u initial ht hu
example (word w time : V) (ht : Stopped (run time (liveValue word w))) :
    terminal word w=run time (liveValue word w) := terminal_eq_run word w time ht
example (raw w : V) : run 1 (liveValue (raw+1) w)=nextValue raw w := run_one_succ raw w
example (raw w : V) : terminal (raw+1) w=
    if ArithmeticCommandStep254.stepValue raw w=0 then 0
    else terminal (ArithmeticCommandWord254.tailValue raw) (ArithmeticCommandStep254.stepValue raw w-1) := terminal_succ raw w
example (raw w : V) : evalValue (raw+1) w=
    if ArithmeticCommandStep254.stepValue raw w=0 then 0
    else evalValue (ArithmeticCommandWord254.tailValue raw) (ArithmeticCommandStep254.stepValue raw w-1) := eval_succ raw w
example (time left right w : V) :
    (∃ t≤time, Stopped (run t (liveValue left w)) ∧ run t (liveValue (appendValue left right) w)=extendValue right (run t (liveValue left w))) ∨
      run time (liveValue (appendValue left right) w)=extendValue right (run time (liveValue left w)) := paired_or_stopped time left right w
example (left right w : V) : ∃ t≤left, Stopped (run t (liveValue left w)) ∧
    run t (liveValue (appendValue left right) w)=extendValue right (terminal left w) := stopped_pair left right w
example (left right w : V) : terminal (appendValue left right) w=
    if terminal left w=0 then 0 else terminal right (working (terminal left w)) := terminal_append left right w
example (left right w : V) : evalValue (appendValue left right) w=
    if evalValue left w=0 then 0 else evalValue right (evalValue left w-1) := eval_append left right w
example (left right w : V) : evalValue (appendValue left right) w=0 ↔
    evalValue left w=0 ∨ (evalValue left w≠0 ∧ evalValue right (evalValue left w-1)=0) := eval_append_eq_zero left right w
example (right w : V) : evalValue (appendValue 0 right) w=evalValue right w := by simp
example (left w : V) : evalValue (appendValue left 0) w=evalValue left w := by rw [ArithmeticCommandWordLaws254.append_right_zero]
example (left right w : V) (hl : evalValue left w=0) : evalValue (appendValue left right) w=0 := by rw [eval_append,if_pos hl]
example (left right w result : V) (hl : evalValue left w=result+1) :
    evalValue (appendValue left right) w=evalValue right result := by simp [eval_append,hl]
example (left right w result : V) (hl : terminal left w=liveValue 0 result) :
    terminal (appendValue left right) w=terminal right result := by simp [terminal_append,hl]
