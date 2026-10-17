import BusyBeaver.ZFC.ArithmeticCommandStepWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254 ArithmeticCommandStepWord254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStepWord254.short_tag_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStepWord254.step_replace
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStepWord254.step_replace_eq_zero
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (k : V) : k < 3 ↔ k = 0 ∨ k = 1 ∨ k = 2 := short_tag_iff k
example (raw rest w : V) : stepValue (replaceValue raw rest) w = stepValue raw w := step_replace raw rest w
example (raw rest w : V) : stepValue (replaceValue raw rest) w = 0 ↔ stepValue raw w = 0 := step_replace_eq_zero raw rest w
example (raw left right w : V) :
    stepValue (replaceValue raw left) w = stepValue (replaceValue raw right) w := by
  rw [step_replace, step_replace]
