import BusyBeaver.ZFC.ArithmeticCommandWordLaws254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandWord254 ArithmeticCommandAppend254 ArithmeticCommandWordLaws254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254.first_replace
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254.tail_replace
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254.replace_twice
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254.replace_own_tail
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254.append_right_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWordLaws254.append_assoc
section IOpen
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (z r : V) : first (replaceValue z r) = first z := first_replace z r
example (z r : V) : tailValue (replaceValue z r) = r := tail_replace z r
example (z r s : V) : replaceValue (replaceValue z r) s = replaceValue z s := replace_twice z r s
example (z : V) : replaceValue z (tailValue z) = z := replace_own_tail z
end IOpen
section ISigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (a : V) : appendValue a 0 = a := append_right_zero a
example (a b c : V) : appendValue (appendValue a b) c = appendValue a (appendValue b c) := append_assoc a b c
example (a b c d : V) : appendValue (appendValue (appendValue a b) c) d =
    appendValue a (appendValue b (appendValue c d)) := by rw [append_assoc, append_assoc]
end ISigma1
