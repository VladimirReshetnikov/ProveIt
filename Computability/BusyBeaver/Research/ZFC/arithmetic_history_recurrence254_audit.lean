import BusyBeaver.ZFC.ArithmeticHistoryRecurrence254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticRow254 ArithmeticHistory254 ArithmeticHistoryRecurrence254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.history_lookup_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.history_lookup
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.quotient_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.tail_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.minor_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.major_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.value_succ_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.value_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.mp_parent_gate
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.mp_parent_children
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.gen_parent_child
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (n i : V) (hi : i ≤ n) : znth (history n) i = value i := history_lookup_le n i hi
example (n i : V) : znth (history n) i = if i ≤ n then value i else 0 := history_lookup n i
example (n : V) : znth (history n) (n + 1) = 0 := by
  rw [history_lookup, if_neg (by simp)]
example (z : V) : z / 12 ≤ z := quotient_le z
example (z : V) : second (z / 12) ≤ z := tail_le z
example (z : V) : first (second (z / 12)) ≤ z := minor_le z
example (z : V) : second (second (z / 12)) ≤ z := major_le z
example (z : V) : value (z + 1) = positiveStep (history z) z := value_succ_step z
example (z : V) : value (z + 1) = rowKernel (z % 12) (z / 12)
    (if z % 12 = 2 then value (second (z / 12)) else value (first (second (z / 12))))
    (value (second (second (z / 12)))) := value_succ z
example (z : V) (ht : z % 12 = 1) (hv : value (z + 1) ≠ 0) :
    MPGate (first (z / 12)) (value (first (second (z / 12))))
      (value (second (second (z / 12)))) := mp_parent_gate z ht hv
example (z : V) (ht : z % 12 = 1) (hv : value (z + 1) ≠ 0) :
    value (first (second (z / 12))) ≠ 0 ∧ value (second (second (z / 12))) ≠ 0 :=
  mp_parent_children z ht hv
example (z : V) (ht : z % 12 = 2) (hv : value (z + 1) ≠ 0) :
    value (second (z / 12)) ≠ 0 := gen_parent_child z ht hv
end Generic
