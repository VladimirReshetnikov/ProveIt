import BusyBeaver.ZFC.ArithmeticStackTail254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticStackTail254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.first_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.second_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.second_lt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_zero_stream
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_shift
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_cantor
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_eq_zero_of_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254.tail_total
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out time initial : V) : tailDef.val.Evalb ![out,time,initial] ↔ out=tailIter time initial := by simp
example (time initial : V) : ∃! out, tailDef.val.Evalb ![out,time,initial] := tail_total time initial
example (initial : V) : tailIter 0 initial=initial := tail_zero initial
example (time initial : V) : tailIter (time+1) initial=second (tailIter time initial) := tail_succ time initial
example : first (0 : V)=0 := first_zero
example : second (0 : V)=0 := second_zero
example (z : V) (hz : z≠0) : second z<z := second_lt z hz
example (time : V) : tailIter time 0=0 := tail_zero_stream time
example (t u initial : V) : tailIter (t+u) initial=tailIter u (tailIter t initial) := tail_add t u initial
example (time initial : V) : tailIter (time+1) initial=tailIter time (second initial) := tail_shift time initial
example (time x z : V) : tailIter (time+1) (cantor x z)=tailIter time z := tail_cantor time x z
example (time initial : V) : tailIter time initial=0 ∨ tailIter time initial+time≤initial := tail_bound time initial
example (time initial : V) (hi : initial≤time) : tailIter time initial=0 := tail_eq_zero_of_le time initial hi
example (initial : V) : tailIter initial initial=0 := tail_eq_zero_of_le initial initial le_rfl
example (initial extra : V) : tailIter (initial+extra) initial=0 := tail_eq_zero_of_le _ _ (by simp)
