import BusyBeaver.ZFC.ArithmeticCommandWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandWord254
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.first_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.second_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.second2_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.second3_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.tail_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.tailValue_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.short_output_bounds
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.long_output_bounds
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.replace_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.tailValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.replaceValue_nat
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (e : Fin 2 → V) : tailDef.val.Evalb e ↔ e 0 = tailValue (e 1) := tail_defined.df e
example (e : Fin 3 → V) : replaceDef.val.Evalb e ↔ e 0 = replaceValue (e 1) (e 2) := replace_defined.df e
example (z : V) : ∃! out, tailDef.val.Evalb ![out,z] := by simp
example (z r : V) : ∃! out, replaceDef.val.Evalb ![out,z,r] := by simp
example (z : V) : tailValue z ≤ z := tailValue_le z
example (z : V) : first z ≤ z := first_le z
example (z : V) : second z ≤ z := second_le z
example (z : V) : second (second z) ≤ z := second2_le z
example (z : V) : second (second (second z)) ≤ z := second3_le z
example (o op x r : V) : (cantor x r ≤ o ∧ o = cantor op (cantor x r)) ↔ o = cantor op (cantor x r) := short_output_bounds _ _ _ _
example (o op x y u r : V) : (cantor u r ≤ o ∧ cantor y (cantor u r) ≤ o ∧ cantor x (cantor y (cantor u r)) ≤ o ∧ o = cantor op (cantor x (cantor y (cantor u r)))) ↔ o = cantor op (cantor x (cantor y (cantor u r))) := long_output_bounds _ _ _ _ _ _
end Generic
example (z : Nat) : tailValue z = CommandWord254.tail z := tailValue_nat z
example (z r : Nat) : replaceValue z r = CommandWord254.replaceRest z r := replaceValue_nat z r
example (c : Enum254.Cmd) (r : Nat) : tailValue (Enum254.pack c r) = r := by
  rw [tailValue_nat, CommandWord254.tail_pack]
example (c : Enum254.Cmd) (old r : Nat) : replaceValue (Enum254.pack c old) r = Enum254.pack c r := by
  rw [replaceValue_nat, CommandWord254.replaceRest_pack]
example (z : Nat) : replaceValue z (tailValue z) = z := by
  rw [replaceValue_nat, tailValue_nat, CommandWord254.replaceRest_self]
example (z r : Nat) : tailValue (replaceValue z r) = r := by
  rw [tailValue_nat, replaceValue_nat, CommandWord254.tail_replaceRest]
-- A large oldrest may be discarded and yield output0.
example (old : Nat) : replaceValue (Enum254.pack (.mp 0) old) 0 = 0 := by
  rw [replaceValue_nat, CommandWord254.replaceRest_pack]
  rfl
example : tailValue (6-1 : Nat) = 1 := by rw [tailValue_nat]; decide
example : tailValue (6 : Nat) = 0 := by rw [tailValue_nat]; decide
example : tailDef.val.Evalb (M := Nat) ![1,5] := by
  simp only [tail_defined.iff]
  change 1 = tailValue 5
  rw [tailValue_nat]
  decide
example : ¬ tailDef.val.Evalb (M := Nat) ![1,6] := by
  simp only [tail_defined.iff]
  change ¬ 1 = tailValue 6
  rw [tailValue_nat]
  decide
